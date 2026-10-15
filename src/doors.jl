# ---------------------------------------------------------------------------
# The Base wrapper's door check (writeup/poc3-plan.md §3.2; the note, "Trait wrappers"
# and "Calls upward"). Base is in the trait world by designation, and a
# specialization of Base reached from a worker is trait-world code when the
# check passes: the layering walk follows calls into Julia's own code, once per
# method instance and process, within a budget, and reports
#   - a call to an inward door (eval, invokelatest outside a declared call,
#     deserialization, reflection over the method table, getglobal on a module,
#     task storage, raw memory): an error at the worker's build, with its line;
#   - a read of a global whose binding does not decide a trait-world type (not
#     constant, or not deeply concrete: `stdout`, the logger's state, `Main`):
#     the same, unless the read is in an outward door's own code;
#   - a call to an outward door (logging, display, printing without an IO):
#     accepted and recorded per worker signature as a dynamic site, which
#     concrete mode reports and `verify_main` binds to the application's sinks;
#   - the budget's end: recorded as "unchecked beyond the budget", never an
#     admission by silence.
# ---------------------------------------------------------------------------

"Inward doors: functions that bring values from code, not from values."
const INWARD_DOORS = Base.IdSet{Any}([
    Core.eval, Base.eval, Base.include, Base.require, Base.invokelatest, Core.invokelatest,
    Base.task_local_storage, Base.unsafe_pointer_to_objref,
    Base.methods, Base.which, Base.hasmethod, Base._methods_by_ftype, Base._which,
    Base.infer_return_type, Base.code_typed, Base.code_lowered, Base.Compiler.return_type,
    Core.getglobal, Base.getglobal, Base.setglobal!, Core.setglobal!,
])
"Outward doors: functions that send values up and bring nothing back."
const OUTWARD_DOORS = Base.IdSet{Any}([
    Base.CoreLogging.handle_message, Base.CoreLogging.shouldlog, Base.CoreLogging.current_logger,
    Base.CoreLogging.current_logger_for_env, Base.CoreLogging.logmsg_shim, Base.CoreLogging.logging_error,
    Base.CoreLogging.min_enabled_level, Base.CoreLogging.global_logger, Base.CoreLogging.with_logger,
    Base.CoreLogging.handle_message_nothrow, Base.fixup_stdlib_path,          # the logging macros' expansion
    Base.display, Base.redisplay, Base.redirect_stdout, Base.redirect_stderr, Base.redirect_stdin,
    Base.Multimedia.displays, Base.Multimedia.pushdisplay, Base.Multimedia.popdisplay,
])
"Outward doors by name, for functions whose no-IO methods read `stdout`: `print`, `println`, `show`, `printstyled`, `flush`, `displaysize()` (`repr` writes to its own buffer)."
const _STDOUT_DOORS = (:print, :println, :show, :printstyled, :flush, :displaysize)

"An inward door reached through a `ccall`."
_inward_ccall(name) = name isa Symbol && name in (:jl_apply, :jl_toplevel_eval, :jl_toplevel_eval_in, :jl_eval_string,
                                                  :jl_expand, :jl_expand_with_loc, :jl_load, :jl_get_global)

"Modules whose functions are inward doors wholesale, when loaded: Serialization (deserialize), Distributed (remotecall)."
function _inward_module(m::Module)
    r = Base.moduleroot(m)
    return nameof(r) in (:Serialization, :Distributed) && owner(r) === :Julia
end

struct DoorFacts
    inward::Vector{String}      # "eval via Base.foo"
    outward::Vector{String}
    globals::Vector{String}     # "Base.stdout (not constant)"
    truncated::Bool
end
const _NO_FACTS = DoorFacts(String[], String[], String[], false)

"Per process: the facts of a Julia method instance, memoized (Base's methods do not change under a session: a pirate of Base is refused)."
const _DOOR_FACTS = IdDict{Core.MethodInstance,DoorFacts}()
"The budget of method instances walked for one worker signature."
const DOOR_BUDGET = Ref(3000)

"Whether `g` is a global whose binding decides a trait-world type: constant, and of a deeply concrete value type, or typed concretely."
function _global_ok(g::GlobalRef)
    isdefined(g.mod, g.name) || return true                    # undefined here: not a value read
    if isconst(g.mod, g.name)
        v = getglobal(g.mod, g.name)
        v isa Module && return true                             # static access to a module's names; a module as a value is caught at the door
        v isa Type && return true
        return deep_concrete(typeof(v))
    end
    T = Core.get_binding_type(g.mod, g.name)
    return T isa Type && deep_concrete(T)
end

"The door facts of a Julia method instance at `world`, walking what it calls, within the budget."
function door_facts(mi::Core.MethodInstance, world::UInt, budget::Ref{Int}, stack::Vector{Core.MethodInstance} = Core.MethodInstance[])
    f0 = get(_DOOR_FACTS, mi, nothing)
    f0 === nothing || return f0
    mi in stack && return _NO_FACTS                             # a cycle: the facts come from the first visit
    if budget[] <= 0
        return DoorFacts(String[], String[], String[], true)
    end
    budget[] -= 1
    m = mi.def
    m isa Method || return _NO_FACTS
    isoutward = m.name in _STDOUT_DOORS || (isdefined(m.module, m.name) && getglobal(m.module, m.name) in OUTWARD_DOORS) ||
                m.module === Base.CoreLogging || m.module === Base.Multimedia
    src = nothing
    try
        for (ci, _) in Base.code_typed_by_type(mi.specTypes; optimize = true, world)
            ci isa Core.CodeInfo && (ci.parent === nothing || ci.parent.def === m) && (src = ci; break)
        end
    catch
    end
    src === nothing && return _NO_FACTS
    inward, outward, globals = String[], String[], String[]
    truncated = false
    sptypes = _CC.sptypes_from_meth_instance(mi)
    here = string(m.module, ".", m.name)
    push!(stack, mi)
    for st in src.code
        ex = st isa Expr && st.head === :(=) ? st.args[2] : st
        if ex isa GlobalRef
            isoutward || _global_ok(ex) || push!(globals, string(ex.mod, ".", ex.name, " read by ", here))
            continue
        end
        ex isa Expr || continue
        if ex.head === :foreigncall
            name = ex.args[1]
            name isa QuoteNode && (name = name.value)
            _inward_ccall(name) && push!(inward, string("ccall ", name, " in ", here))
            continue
        end
        for a in ex.args
            a isa GlobalRef && !isoutward && !_global_ok(a) && push!(globals, string(a.mod, ".", a.name, " read by ", here))
        end
        if ex.head === :invoke
            c = ex.args[1]
            cmi = c isa Core.CodeInstance ? c.def : c
            isdefined(Core, :ABIOverride) && cmi isa Core.ABIOverride && (cmi = cmi.def)
            cmi isa Core.MethodInstance || continue
            cm = cmi.def
            cm isa Method || continue
            f = isdefined(cm.module, cm.name) ? getglobal(cm.module, cm.name) : nothing
            if f in INWARD_DOORS || _inward_module(cm.module)
                push!(inward, string(cm.module, ".", cm.name, " called by ", here))
            elseif f in OUTWARD_DOORS || cm.name in _STDOUT_DOORS && length(Base.unwrap_unionall(cm.sig).parameters) >= 2 &&
                   !(Base.unwrap_unionall(cm.sig).parameters[2] <: IO)
                push!(outward, string(cm.module, ".", cm.name, " called by ", here))
            elseif owner(cm.module) === :Julia
                sub = door_facts(cmi, world, budget, stack)
                append!(inward, sub.inward); append!(outward, sub.outward); append!(globals, sub.globals)
                truncated |= sub.truncated
            end
        elseif ex.head === :call
            fT = _CC.argextype(ex.args[1], src, sptypes)
            f = fT isa _CC.Const ? fT.val : (Base.issingletontype(_CC.widenconst(fT)) ? _CC.widenconst(fT).instance : nothing)
            f === nothing && continue
            if (f === Base.invokelatest || f === Core.invokelatest) && _latest_outward(src, sptypes, ex)
                push!(outward, string("invokelatest of an outward door in ", here))
            elseif f in INWARD_DOORS
                push!(inward, string(f, " called by ", here))
            elseif (f === Core.getfield || f === Base.getproperty) && length(ex.args) >= 3 &&
                   _CC.widenconst(_CC.argextype(ex.args[2], src, sptypes)) <: Module && !_static_access(src, sptypes, ex)
                push!(inward, string("getglobal by name (a module's field looked up at run time) in ", here))
            elseif f in OUTWARD_DOORS || (f isa Function && nameof(f) in _STDOUT_DOORS && parentmodule(f) === Base &&
                                           (length(ex.args) < 2 || !(_CC.widenconst(_CC.argextype(ex.args[2], src, sptypes)) <: IO)))
                push!(outward, string(f, " called by ", here))
            end
            # a dynamic call is not followed. The design checks its target when it
            # compiles; on stock Julia nothing does (the audit follows static
            # edges only), so a door behind a dynamic call is a PoC limit.
        end
    end
    pop!(stack)
    facts = DoorFacts(unique!(inward), unique!(outward), unique!(globals), truncated)
    _DOOR_FACTS[mi] = facts
    return facts
end

"`getproperty(m, s)` with a constant module and symbol is a static global reference, not a door."
_static_access(src, sptypes, ex) = all(a -> (t = _CC.argextype(a, src, sptypes); t isa _CC.Const || a isa QuoteNode), ex.args[2:min(3, end)])

"The `GlobalRef` a static `getproperty(m, s)` stands for, or `nothing`."
function _static_ref(src, sptypes, ex)
    length(ex.args) >= 3 || return nothing
    m = _CC.argextype(ex.args[2], src, sptypes)
    s = ex.args[3] isa QuoteNode ? ex.args[3].value : (t = _CC.argextype(ex.args[3], src, sptypes); t isa _CC.Const ? t.val : nothing)
    m isa _CC.Const && m.val isa Module && s isa Symbol || return nothing
    return GlobalRef(m.val, s)
end

"`invokelatest(f, …)` with a constant `f` that is an outward door is the door, not the inward one (the logging macros expand to it)."
function _latest_outward(src, sptypes, ex)
    length(ex.args) >= 2 || return false
    t = _CC.argextype(ex.args[2], src, sptypes)
    f = t isa _CC.Const ? t.val : (Base.issingletontype(_CC.widenconst(t)) ? _CC.widenconst(t).instance : nothing)
    return f !== nothing && f in OUTWARD_DOORS
end

"The outward doors and the budget's end, per worker signature: what concrete mode reports and verify_main binds."
const WORKER_DOORS = IdDict{Any,DoorFacts}()

"The state of one worker check's walk into Base: the budget and the outward doors found."
mutable struct _DoorWalk
    budget::Base.RefValue{Int}
    outward::Vector{String}
    truncated::Bool
end
const _WALK = Ref{Union{Nothing,_DoorWalk}}(nothing)

"At a worker's call into Julia's code: the door facts of the specialization reached, reported at the worker's line."
function _doors!(out, @nospecialize(csig), src, mi, i, world)
    st = _WALK[]
    st === nothing && return nothing
    tmi = _target_mi(csig, world)
    tmi === nothing && return nothing
    facts = door_facts(tmi, world, st.budget)
    line = _line_of(src, mi, i)
    for d in facts.inward
        push!(out, "$line: reaches an inward door through Julia's code: $d. A value denoting code has no bound; " *
                   "a trait module may declare the call (@call), with a checked result")
    end
    for g in facts.globals
        push!(out, "$line: reads a global that does not decide a trait-world type: $g")
    end
    for d in facts.outward
        push!(st.outward, "$line: $d")
    end
    facts.truncated && (st.truncated = true)
    return nothing
end
