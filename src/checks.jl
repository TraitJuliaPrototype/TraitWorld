# ---------------------------------------------------------------------------
# What library code may do with a trait object (rule 2 and the "may do"
# table), checked on the worker's typed code at a concrete representation:
# a `TObj` may reach only methods declared for trait objects, which are the
# trait's operations and workers whose bounds it carries. Anything else, a
# builtin (`t.field`, `typeof(t)`, storing it in a tuple), an ordinary
# function (`sum(t)`) or the entry of a function bounded by another trait, is
# reported with its line. Workers called from workers are checked too.
# ---------------------------------------------------------------------------

const _CC = Core.Compiler

struct TraitUseError <: Exception
    problems::Vector{String}
end
function Base.showerror(io::IO, e::TraitUseError)
    print(io, "TraitUseError: library code breaks a rule of the trait world:")
    for p in e.problems
        print(io, "\n  ", p)
    end
end

_istobj(@nospecialize(T)) = T isa DataType && T.name === Base.typename(TObj)
_ishandle(@nospecialize(T)) = T isa DataType && T <: Handle
_hastobj(@nospecialize(T)) = _istobj(T) || (T isa Union && any(_istobj, Base.uniontypes(T)))

function _line_of(src, mi, i)
    try
        lin = Base.IRShow.buildLineInfoNode(src.debuginfo, mi, i)
        if !isempty(lin)
            n = lin[end]
            return string(basename(string(n.file)), ":", n.line)
        end
    catch
    end
    m = mi isa Core.MethodInstance ? mi.def : nothing
    return m isa Method ? string(basename(string(m.file)), ":", m.line) : "?"
end

"Whether `f` is an operation function of one of the traits in `lb` (its methods on trait objects forward)."
function _is_op(@nospecialize(f), @nospecialize(lb))
    for X in Base.uniontypes(lb)
        is_trait(X) || continue
        for op in _ops(X)
            _opfn(X, op) === f && return true
        end
    end
    return false
end

"`Type{<:TObj}` or `Type{<:CObj}`: a declaration of the machinery's own types, not a look at the user's."
_handle_type(@nospecialize(T)) = T isa DataType && T <: Type && (T.parameters[1] <: TObj || T.parameters[1] <: CObj)

_traitnames(@nospecialize(T)) = _istobj(T) ? join(string.(Base.uniontypes(T.parameters[1])), ", ") : string(T)

"""
    worker_problems(sig) -> Vector{String}

Problems in the worker selected by the concrete call signature `sig`, and in
the workers it calls.
"""
_escapes(@nospecialize(T)) = T isa Union ? any(_escapes, Base.uniontypes(T)) :
    (T isa DataType && (T <: TObj || T <: View || T <: CObj || T <: CMulti ||
                        (T <: Tuple && any(_escapes, T.parameters))))

function worker_problems(@nospecialize(sig), seen = Base.IdSet{Any}(), out = String[]; root::Bool = true)
    sig in seen && return out
    push!(seen, sig)
    if root && _WALK[] === nothing
        # the root call owns the walk into Base: a budget, and the outward doors recorded per signature
        st = _DoorWalk(Ref(DOOR_BUDGET[]), String[], false)
        _WALK[] = st
        try
            _worker_problems(sig, seen, out, true)
        finally
            _WALK[] = nothing
        end
        WORKER_DOORS[sig] = DoorFacts(String[], st.outward, String[], st.truncated)
        # the budget's end is reported whatever the concrete level: never an admission by silence
        st.truncated && Base.inferencebarrier(_warn_truncated)(sig)
        return out
    end
    return _worker_problems(sig, seen, out, root)
end

function _warn_truncated(@nospecialize(sig))
    @warn "The door check of $(sig) stopped at its budget ($(DOOR_BUDGET[]) method instances): " *
          "the code beyond it is unchecked for inward doors (raise TraitWorld.DOOR_BUDGET[] to check it)" maxlog = 1 _id = hash(sig)
    return nothing
end

function _worker_problems(@nospecialize(sig), seen, out, root::Bool)
    world = Base.get_world_counter()
    for (src, rt) in Base.code_typed_by_type(sig; optimize = false, world)
        mi = src.parent
        if root && _escapes(rt)
            m = mi isa Core.MethodInstance ? mi.def : nothing
            push!(out, "$(m isa Method ? string(basename(string(m.file)), ":", m.line) : "?"): returns a trait object " *
                       "to ordinary code: a trait object is a handle, not a value")
        end
        sptypes = mi isa Core.MethodInstance ? _CC.sptypes_from_meth_instance(mi) : _CC.EMPTY_SPTYPES
        for (i, st) in enumerate(src.code)
            ex = st isa Expr && st.head === :(=) ? st.args[2] : st
            # globals the worker's own code reads must decide a trait-world type
            if ex isa GlobalRef
                _global_ok(ex) || push!(out, "$(_line_of(src, mi, i)): reads the global `$(ex.mod).$(ex.name)`, which does not decide a trait-world type (not a constant, or not deeply concrete)")
                continue
            end
            if ex isa Expr
                for a in ex.args
                    a isa GlobalRef && !_global_ok(a) &&
                        push!(out, "$(_line_of(src, mi, i)): reads the global `$(a.mod).$(a.name)`, which does not decide a trait-world type (not a constant, or not deeply concrete)")
                end
            end
            if ex isa Expr && ex.head === :new
                # a closure capturing a trait object: its body runs wherever it is called
                # (inside Base's `sum`, say), so check it here, for any arguments
                CT = _CC.argextype(ex.args[1], src, sptypes)
                CT = CT isa _CC.Const ? CT.val : _CC.widenconst(CT)
                CT isa Type && CT <: Type && (CT = CT.parameters[1])
                if CT isa DataType && CT <: Function && any(k -> _hastobj(fieldtype(CT, k)), 1:fieldcount(CT))
                    for mm in Base._methods_by_ftype(Tuple{CT,Vararg{Any}}, -1, world)
                        n = mm.method.nargs - 1
                        worker_problems(Tuple{CT,ntuple(_ -> Any, n)...}, seen, out)
                    end
                end
                continue
            end
            ex isa Expr && ex.head === :call || continue
            ats = Any[_CC.widenconst(_CC.argextype(a, src, sptypes)) for a in ex.args]
            fT = _CC.argextype(ex.args[1], src, sptypes)
            f = fT isa _CC.Const ? fT.val : (Base.issingletontype(_CC.widenconst(fT)) ? _CC.widenconst(fT).instance : nothing)
            if !any(k -> _hastobj(ats[k]), 2:length(ats))
                if any(k -> _ishandle(ats[k]), 2:length(ats)) && (f === Core.getfield || f === Base.getproperty ||
                   f === Core.setfield! || f === Base.setproperty! || f === Core.typeof || f === Base.fieldtype)
                    push!(out, "$(_line_of(src, mi, i)): `h.ref` or `typeof(h)` on a handle: a handle is opaque inside the trait world, " *
                               "a value to pass to the next declared call")
                    continue
                end
                _layering!(out, seen, f, ats, src, mi, i, world)
                continue
            end
            line = _line_of(src, mi, i)
            if f === nothing
                push!(out, "$line: a trait object is passed to a function not known at compile time")
                continue
            end
            if f isa DeclaredCall
                push!(out, "$line: a trait object is passed to the declared call $f: trait objects never go up; pass what its operations return")
                continue
            end
            fname = f isa Function ? nameof(f) : f
            f === Core._typeof_captured_variable && continue      # closure lowering: the closure body is checked at its `new`
            if (f === Core.isa || f === Core.typeassert) && length(ats) == 3 && _handle_type(ats[3])
                continue                                           # a keyword sorter's own check of a bounded keyword
            end
            if f isa Core.Builtin || f isa Core.IntrinsicFunction
                what = f === Core.getfield ? "`t.field`: the user's data is reached only through the trait's operations" :
                       f === Core.typeof ? "`typeof(t)`: code must not depend on the user's type" :
                       f === Core.tuple ? "stored in a tuple: a trait object is a handle, not a value" :
                       f === Core._apply_iterate ? "splatted into a call" :
                       "passed to the builtin `$fname`"
                push!(out, "$line: $what")
                continue
            end
            csig = Tuple{ats...}
            ms = Base._methods_by_ftype(csig, -1, world)
            if !(ms isa Vector) || isempty(ms)
                push!(out, "$line: `$fname` has no method for a trait object carrying $(_traitnames(ats[findfirst(k -> k > 1 && _hastobj(ats[k]), 1:length(ats))]))")
                continue
            end
            for mm in ms
                m = mm.method
                msig = Base.unwrap_unionall(m.sig)
                params = msig.parameters
                for k in 2:length(ats)
                    _hastobj(ats[k]) || continue
                    p = k <= length(params) ? params[k] : (isempty(params) ? Any : params[end])
                    p isa Core.TypeofVararg && (p = isdefined(p, :T) ? p.T : Any)
                    lb = _tobj_lb(p)
                    if lb === nothing
                        if f isa Function && !isempty(traits_at(f, k - 1, length(ats) - 1))
                            push!(out, "$line: a trait object carrying $(_traitnames(ats[k])) is passed to `$fname`, whose " *
                                       "methods need other traits at argument $(k-1). Declare the bounds it needs, so the caller projects each (rule 2)")
                        elseif f === Base.getproperty || f === Base.setproperty!
                            push!(out, "$line: `t.field`: the user's data is reached only through the trait's operations")
                        else
                            push!(out, "$line: a trait object carrying $(_traitnames(ats[k])) is passed to `$fname`, an ordinary " *
                                       "function: it can do only what its traits declare. Declare `$fname` as an operation, or use the operations")
                        end
                    elseif !_is_op(f, lb)
                        # a worker called from a worker: checked too, at whatever argument types it gets
                        worker_problems(csig, seen, out; root = false)
                    end
                end
            end
        end
    end
    return out
end

"""
Rule 1 on typed code: a call that resolves to a method outside the trait
world (a package the module never imported, reached as `Main.Plain.f()`) is
reported; calls into helpers of trait modules are followed.
"""
function _layering!(out, seen, @nospecialize(f), ats, src, mi, i, world)
    (f === nothing || f isa Core.Builtin || f isa Core.IntrinsicFunction) && return nothing
    csig = Tuple{ats...}
    ms = Base._methods_by_ftype(csig, -1, world)
    ms isa Vector || return nothing
    for mm in ms
        m = mm.method
        if !is_trait_world(m.module)
            push!(out, "$(_line_of(src, mi, i)): calls $(m.module).$(m.name), outside the trait world (rule 1): " *
                       "the trait world uses only itself")
        elseif Base.moduleroot(m.module) === TraitWorld
            continue                                      # the machinery: declared calls, operations, checked calls
        elseif _is_entry(m)
            continue                                      # a plain value into another function's entry: its worker is checked at its own first call
        elseif owner(Base.moduleroot(m.module)) !== :Julia
            worker_problems(csig, seen, out; root = false)
        elseif f === Base.getproperty && length(ats) >= 3 && ats[2] <: Module
            # `Mod.name` with constants is a static global reference, checked as one; with a
            # symbol computed at run time it is the getglobal door
            st0 = src.code[i]
            ex0 = st0 isa Expr && st0.head === :(=) ? st0.args[2] : st0
            sp0 = _CC.sptypes_from_meth_instance(mi)
            if _static_access(src, sp0, ex0)
                g = _static_ref(src, sp0, ex0)
                g === nothing || _global_ok(g) ||
                    push!(out, "$(_line_of(src, mi, i)): reads the global `$(g.mod).$(g.name)`, which does not decide a trait-world type (not a constant, or not deeply concrete)")
            else
                push!(out, "$(_line_of(src, mi, i)): looks a module's field up by a name computed at run time (the getglobal door): a value denoting code has no bound")
            end
        elseif (f === Base.invokelatest || f === Core.invokelatest) &&
               (st0 = src.code[i]; ex0 = st0 isa Expr && st0.head === :(=) ? st0.args[2] : st0; _latest_outward(src, _CC.sptypes_from_meth_instance(mi), ex0))
            st = _WALK[]
            st === nothing || push!(st.outward, "$(_line_of(src, mi, i)): invokelatest of an outward door")
        elseif f in INWARD_DOORS
            push!(out, "$(_line_of(src, mi, i)): calls the inward door `$(nameof(f))`: a value denoting code has no bound; " *
                       "a trait module may declare the call (@call), with a checked result")
        elseif f in OUTWARD_DOORS || (f isa Function && nameof(f) in _STDOUT_DOORS && parentmodule(f) === Base && (length(ats) < 2 || !(ats[2] <: IO)))
            st = _WALK[]
            st === nothing || push!(st.outward, "$(_line_of(src, mi, i)): $(nameof(f))")
        else
            _doors!(out, csig, src, mi, i, world)         # Base's code, checked through the door list
        end
    end
    return nothing
end

"""
    checked_call(f, args...)

How an entry calls a worker. A generated function: each call signature gets
its own flag, embedded in its compiled code, so the check runs once per
signature, and the flag is saved with whichever package image compiled that
signature (rule 4 places it). The call to the worker is static.
"""
@generated function checked_call(f, args...)
    flag = Ref(false)
    guard = GuardState()
    sig = Tuple{f,args...}
    return quote
        # a dynamic call: the check's reflection stays out of compiled code (and out of trimmed binaries)
        $(flag)[] || CLOSED_WORLD[] || Base.inferencebarrier(_check_once)($flag, $sig)
        _guard($guard, $sig)
        return _noescape(f(args...))
    end
end

"""
    checked_kwcall(nt, f, args...)

`checked_call` for a function with keyword arguments: the supplied keywords,
bounded ones already projected, go to the worker's own keyword sorter, which
fills the defaults inside the trait world.
"""
@generated function checked_kwcall(nt::NamedTuple, f, args...)
    flag = Ref(false)
    guard = GuardState()
    sig = Tuple{typeof(Core.kwcall),nt,f,args...}
    return quote
        $(flag)[] || CLOSED_WORLD[] || Base.inferencebarrier(_check_once)($flag, $sig)
        _guard($guard, $sig)
        return _noescape(Core.kwcall(nt, f, args...))
    end
end

"The function a worker signature belongs to: through `Core.kwcall` for a keyword worker."
_worker_ftype(@nospecialize(sig)) = sig.parameters[1] === typeof(Core.kwcall) ? sig.parameters[3] : sig.parameters[1]

# a trait object never reaches ordinary code: one dispatch at the boundary, folded per signature
@inline _noescape(x) = x
_noescape(::Union{TObj,View,CObj,CMulti}) = throw(TraitUseError(["a trait object was returned to ordinary code: a trait object is a handle, not a value"]))

@noinline function _check_once(flag::Base.RefValue{Bool}, @nospecialize(sig))
    CLOSED_WORLD[] && (flag[] = true; return nothing)      # checked by verify_main at build time
    sig in _VC_CHECKED && (flag[] = true; return nothing)   # checked when its view cache was built
    ps = Base.invokelatest(worker_problems, sig)::Vector{String}
    isempty(ps) || throw(TraitUseError(unique(ps)))
    Base.invokelatest(_check_concrete, sig)
    flag[] = true
    _vc_note_worker(sig)                                   # compiled in this session: for a view cache
    return nothing
end
