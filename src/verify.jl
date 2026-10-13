# ---------------------------------------------------------------------------
# verify_main, ported from TraitRegions: does a program only ever run
# compiled code? Walk the optimized code reachable from `main(argtypes...)`
# and classify every call:
#
#   static       an `invoke` of a known CodeInstance;
#   bounded      a dynamic call whose targets are finitely many and known now;
#   trait        a dynamic call of TraitWorld's entries: the builder per user
#                type (`enter`), the worker per signature (`checked_call`), a
#                function argument's wrapper (`enter_callable`). Their targets
#                are enumerated from the program's argument types and the
#                registered projections and implementations;
#   root         a closure handed to the runtime (task, atexit, finalizer);
#   guard        the machinery's slow paths (checks, the audit, reflection):
#                not followed, a verified closed-world build runs them now;
#   hole         anything else.
#
# A hole on an error path (every path from it ends in an uncaught throw) runs
# only while the program is dying of an exception. The verdict holds for the
# world that exists when it runs.
# ---------------------------------------------------------------------------


struct Hole
    kind::Symbol            # :dispatch, :callee, :splat, :latest, :builtin, :inference, :eval, :closure, :trait_arg, :noscan
    errorpath::Bool
    caller::Core.MethodInstance
    stmt::Int
    callee::Any
    argtypes::Any
    line::String
end

struct _Site
    kind::Symbol            # :bounded, :trait, :root, :guard, or a hole kind
    doomed::Bool            # every path from it ends in an uncaught throw (in this function)
    intry::Bool             # inside a `try` of this function
    stmt::Int
    callee::Any
    argtypes::Any
    targets::Vector{Core.MethodInstance}
    line::String
end

struct _Scan
    invokes::Vector{Tuple{Core.MethodInstance,Bool,Bool}}   # static callee, doomed, intry
    sites::Vector{_Site}
    throws::Bool            # every path from the entry ends in an uncaught throw
    returns::Bool           # some path from the entry returns a value
end

"Result of [`verify_main`](@ref)."
struct MainReport
    entry::Any
    reached::Int                    # MethodInstances in the closure
    normal::Int                     # of which reached on a normal path
    static_calls::Int
    bounded::Int                    # dynamic calls with an enumerated target set
    trait_sites::Int                # dynamic calls made by the trait machinery
    targets::Vector{Pair{Symbol,Any}}   # their targets: kind => signature
    roots::Int                      # closures handed to the runtime, followed
    guard_sites::Int
    holes::Vector{Hole}
    uncompiled::Vector{Any}         # normal-path MethodInstances without native code
    checked_native::Bool            # false while generating a package image
    findings::Vector{Pair{Any,Vector{PiracyFinding}}}
    problems::Vector{String}        # build-time checks of the enumerated workers (rules 1 and 3)
end

"`true` iff no hole lies on a normal path and every normal-path method instance has native code."
isclosed(r::MainReport) = !any(h -> !h.errorpath, r.holes) && isempty(r.uncompiled)

# --- target method instances -------------------------------------------------

"The MethodInstance a call with signature `S` runs (its compileable specialization)."
function _target_mi(@nospecialize(S), world::UInt)
    match = Base._which(S; world, raise = false)
    match === nothing && return nothing
    csig = _CC.get_compileable_sig(match.method, match.spec_types, match.sparams)
    if csig !== nothing && csig !== match.spec_types
        m2 = Base._which(csig; world, raise = false)
        m2 === nothing || (match = m2)
    end
    return _CC.specialize_method(match)
end

"A type that dispatch sees as one runtime type (values of `DataType` etc. dispatch as `Type{value}`)."
_isleaf(@nospecialize(A)) =
    _CC.isType(A) ? !Base.has_free_typevars(A) : (Base.isdispatchelem(A) && !(A <: Type))

function _union_split(argtypes::Vector{Any}, limit::Int)
    combos = Vector{Any}[Any[]]
    for A in argtypes
        parts = _isleaf(A) ? Any[A] : A isa Union ? Base.uniontypes(A) : nothing
        parts === nothing && return nothing
        all(_isleaf, parts) || return nothing
        length(combos) * length(parts) > limit && return nothing
        combos = Vector{Any}[Any[c..., p] for c in combos for p in parts]
    end
    return combos
end

"""
`@nospecialize` makes Julia compile one instance for a position only if the
declared type there mentions no type variable of the method: for
`f(@nospecialize(x::T)) where T` it still specializes per runtime type.
"""
function _nospecialized(m::Method, i::Int)
    k = min(i, m.nargs - 1)                  # a Vararg tail shares the last bit
    (m.nospecialize >> (k - 1)) & 1 == 1 || return false
    ps = Base.unwrap_unionall(m.sig).parameters
    d = ps[min(i + 1, length(ps))]
    if Base.isvarargtype(d)
        d = isdefined(d, :T) ? d.T : Any
    end
    return !Base.has_free_typevars(d)
end

"Targets of a dynamic call to a known function, or `nothing` if they depend on unenumerated runtime types."
function _bounded_targets(@nospecialize(f), argtypes::Vector{Any}, world::UInt)
    ft = Core.Typeof(f)
    out = Core.MethodInstance[]
    combos = _union_split(argtypes, 32)
    if combos !== nothing
        for c in combos
            mi = _target_mi(Tuple{ft, c...}, world)
            mi === nothing || push!(out, mi)
        end
        return out
    end
    any(A -> A === Union{}, argtypes) && return out
    ms = Base._methods_by_ftype(Tuple{ft, argtypes...}, -1, world)
    ms isa Vector || return nothing
    for match in ms
        m = match.method
        sp = match.spec_types
        sp isa DataType || return nothing
        for (i, A) in enumerate(argtypes)
            _isleaf(A) && continue
            # the method itself fixes this position (a method for a concrete type) ...
            i + 1 <= length(sp.parameters) && !Base.isvarargtype(sp.parameters[i+1]) &&
                _isleaf(sp.parameters[i+1]) && continue
            # ... or does not specialize on it
            _nospecialized(m, i) && continue
            return nothing
        end
        csig = _CC.get_compileable_sig(m, match.spec_types, match.sparams)
        mi = _target_mi(csig === nothing ? match.spec_types : csig, world)
        mi === nothing || push!(out, mi)
    end
    return out
end

# --- reading optimized code ----------------------------------------------------

function _constval(src, sptypes, @nospecialize(x))
    t = _CC.argextype(x, src, sptypes)
    t isa _CC.Const && return Some{Any}(t.val)
    T = _CC.widenconst(t)
    Base.issingletontype(T) && return Some{Any}(T.instance)
    return nothing
end

_argT(src, sptypes, @nospecialize(x)) = _CC.widenconst(_CC.argextype(x, src, sptypes))

"Resolve a callee: `(:const, f)`, `(:field, objtype, name, obj)` or `(:unknown, type)`."
function _callee(src, sptypes, @nospecialize(x))
    if x isa Core.SSAValue
        d = src.code[x.id]
        if Meta.isexpr(d, :call) && length(d.args) >= 3
            g = _constval(src, sptypes, d.args[1])
            if g !== nothing && something(g) === Core.getfield && d.args[3] isa QuoteNode
                return (:field, _argT(src, sptypes, d.args[2]), d.args[3].value, d.args[2])
            elseif g !== nothing && something(g) === Core.compilerbarrier
                h = _constval(src, sptypes, d.args[3])
                h === nothing || return (:const, something(h))
            end
        end
    end
    v = _constval(src, sptypes, x)
    v === nothing || return (:const, something(v))
    return (:unknown, _argT(src, sptypes, x))
end

"Name of the field `x` was loaded from, if it is a `getfield(obj, :name)` result."
function _fieldof(src, @nospecialize(x))
    x isa Core.SSAValue || return nothing
    d = src.code[x.id]
    while d isa Core.PiNode && d.val isa Core.SSAValue
        d = src.code[d.val.id]
    end
    Meta.isexpr(d, :call) && length(d.args) >= 3 && d.args[3] isa QuoteNode || return nothing
    return d.args[3].value
end

function _succs(src)
    code = src.code
    n = length(code)
    succ = [Int[] for _ in 1:n]
    for i in 1:n
        st = code[i]
        nxt = i < n ? i + 1 : 0
        if st isa Core.GotoNode
            push!(succ[i], st.label)
        elseif st isa Core.GotoIfNot
            push!(succ[i], st.dest); nxt > 0 && push!(succ[i], nxt)
        elseif st isa Core.ReturnNode
        elseif st isa Core.EnterNode
            st.catch_dest == 0 || push!(succ[i], st.catch_dest); nxt > 0 && push!(succ[i], nxt)
        elseif src.ssavaluetypes[i] === Union{} &&
               (Meta.isexpr(st, :call) || Meta.isexpr(st, :invoke) || Meta.isexpr(st, :foreigncall))
        else
            nxt > 0 && push!(succ[i], nxt)
        end
    end
    return succ
end

"Statements inside a `try` of this function (an over-approximation: from each `EnterNode` up to a `leave`)."
function _intry(src, succ)
    n = length(src.code)
    intry = falses(n)
    for e in 1:n
        src.code[e] isa Core.EnterNode || continue
        stack = Int[e + 1]
        while !isempty(stack)
            j = pop!(stack)
            1 <= j <= n && !intry[j] || continue
            Meta.isexpr(src.code[j], :leave) && continue
            intry[j] = true
            append!(stack, succ[j])
        end
    end
    return intry
end

function _reaches_return(src, succ)
    n = length(src.code)
    seen = falses(n)
    stack = Int[1]
    while !isempty(stack)
        j = pop!(stack)
        1 <= j <= n && !seen[j] || continue
        seen[j] = true
        st = src.code[j]
        st isa Core.ReturnNode && isdefined(st, :val) && return true
        append!(stack, succ[j])
    end
    return false
end

_throw_ccall(name) = name isa Symbol && (occursin("throw", String(name)) || occursin("error", String(name)))

"""
Statements from which every path ends in a throw that this function does not
catch: least fixpoint from the throw sinks (`throw`, `rethrow`, error ccalls,
invokes of functions that only throw, dynamic calls inferred `Union{}` other
than `exit`). Exits and endless loops are not doomed.
"""
function _doomed(src, succ, intry, throws_only)
    code = src.code
    n = length(code)
    sink = falses(n)
    for i in 1:n
        intry[i] && continue
        st = code[i]
        src.ssavaluetypes[i] === Union{} || continue
        if Meta.isexpr(st, :call)
            # inference proved the call never returns: every target throws, or
            # exits, or loops. As trim does, take it as a throw, except `exit`.
            f = st.args[1]
            f isa GlobalRef && isdefined(f.mod, f.name) && (f = getglobal(f.mod, f.name))
            sink[i] = f !== Base.exit
        elseif Meta.isexpr(st, :foreigncall)
            name = st.args[1]
            name isa QuoteNode && (name = name.value)
            sink[i] = _throw_ccall(name)
        elseif Meta.isexpr(st, :invoke)
            # the call site is typed Union{}; the callee only fails to throw if
            # it can neither throw nor return on its own (it exits or loops). A
            # callee that can return is typed Union{} here through what the
            # caller knows (constant propagation): it throws in this context.
            c = st.args[1]
            cmi = c isa Core.CodeInstance ? c.def : c
            isdefined(Core, :ABIOverride) && cmi isa Core.ABIOverride && (cmi = cmi.def)
            sink[i] = cmi isa Core.MethodInstance && throws_only(cmi)
        end
    end
    doomed = copy(sink)
    changed = true
    while changed
        changed = false
        for i in n:-1:1
            doomed[i] && continue
            s = succ[i]
            isempty(s) && continue
            if all(j -> 1 <= j <= n && doomed[j], s)
                doomed[i] = true
                changed = true
            end
        end
    end
    return doomed
end

function _line(src, mi, i)
    try
        lin = Base.IRShow.buildLineInfoNode(src.debuginfo, mi, i)
        if !isempty(lin)
            n = lin[end]
            return string(n.file, ":", n.line)
        end
    catch
    end
    m = mi.def
    return m isa Method ? string(m.file, ":", m.line) : ""
end

# ccalls that run arbitrary code or the compiler
const _EVAL_CCALLS = (:jl_apply, :jl_toplevel_eval, :jl_toplevel_eval_in, :jl_eval_string,
                      :jl_compile_hint, :jl_expand, :jl_expand_with_loc)

_dispatching_builtin(@nospecialize(f)) =
    f === Core._apply || f === Core._apply_iterate || f === Core._call_in_world_total ||
    f === Core.invoke || f === Core.invoke_in_world || f === Core.invokelatest ||
    f === Core.finalizer || f === Core.modifyfield! || f === Core.modifyglobal! ||
    f === Core.memoryrefmodify!

function _is_return_type(@nospecialize(f))
    f === _CC.return_type && return true
    isdefined(Base, :Compiler) && isdefined(Base.Compiler, :return_type) && f === Base.Compiler.return_type
end

# --- the walk ----------------------------------------------------------------------

mutable struct _Walk
    world::UInt
    scans::IdDict{Core.MethodInstance,_Scan}
    active::Base.IdSet{Core.MethodInstance}
    plans::Vector{Any}                          # (cache, U, builder): entry caches to fill for a closed world
    views::Base.IdSet{Core.MethodInstance}      # entries analyzed at a call site's types (never compiled as such)
    native_only::Base.IdSet{Core.MethodInstance}   # the entries' real instances: checked for native code only
end
_Walk(world::UInt) = _Walk(world, IdDict{Core.MethodInstance,_Scan}(), Base.IdSet{Core.MethodInstance}(), Any[],
                           Base.IdSet{Core.MethodInstance}(), Base.IdSet{Core.MethodInstance}())

"An entry's code at narrower argument types, for analysis only."
function _view_mi(m::Method, @nospecialize(sig), world::UInt)
    match = Base._which(sig; world, raise = false)
    match === nothing && return nothing
    match.method === m || return nothing
    return _CC.specialize_method(m, sig, match.sparams)
end

function _get_scan(cx::_Walk, mi::Core.MethodInstance)
    sc = get(cx.scans, mi, nothing)
    sc === nothing || return sc
    mi in cx.active && return nothing                  # a cycle: callers assume "may return"
    push!(cx.active, mi)
    sc = try
        _scan(mi, cx)
    finally
        delete!(cx.active, mi)
    end
    cx.scans[mi] = sc
    return sc
end

"A `Union{}`-typed call of `mi` is a throw unless `mi` can neither throw nor return (it exits or loops)."
function _throws_only(cx::_Walk, mi::Core.MethodInstance)
    sc = _get_scan(cx, mi)
    return sc !== nothing && (sc.throws || sc.returns)
end

"Closure handed to the runtime: `(f, argtypes)` if statement `st` registers one."
function _runtime_closure(src, sptypes, @nospecialize(st))
    if Meta.isexpr(st, :foreigncall)
        name = st.args[1]
        name isa QuoteNode && (name = name.value)
        name === :jl_new_task && length(st.args) >= 6 &&
            return (:task, Any[_argT(src, sptypes, st.args[6])])
        return nothing
    end
    Meta.isexpr(st, :invoke) || Meta.isexpr(st, :call) || return nothing
    off = Meta.isexpr(st, :invoke) ? 1 : 0
    length(st.args) >= 2 + off || return nothing
    fv = _constval(src, sptypes, st.args[1+off])
    fv === nothing && return nothing
    f = something(fv)
    ats = Any[_argT(src, sptypes, a) for a in st.args[2+off:end]]
    if f === Core.Task && length(ats) >= 1
        return (:task, Any[ats[1]])
    elseif f === Base.atexit && length(ats) == 1
        return (:atexit, Any[ats[1]])
    elseif (f === Base.finalizer || f === Core.finalizer) && length(ats) == 2
        return (:finalizer, Any[ats[1], ats[2]])
    end
    return nothing
end

# the machinery's slow paths: reflection, checks, the audit. Not followed: in a
# closed world they are switched off and verify_main runs them at build time.
_machinery_method(m::Method) = m.module === TraitWorld && m.name in
    (:_check_once, :_enter_slow, :_guard_slow, :_builder, :worker_problems, :audit, :_rule3_error,
     :_closed_miss, :_witness, :witness, :proj_lookup)

const _ENTER = Ref{Any}(nothing)
const _ENTER_CALLABLE = Ref{Any}(nothing)
_enter_method() = something(_ENTER[] === nothing ? (_ENTER[] = only(methods(enter))) : _ENTER[])
_enter_callable_method() = something(_ENTER_CALLABLE[] === nothing ? (_ENTER_CALLABLE[] = only(methods(enter_callable))) : _ENTER_CALLABLE[])

"User types a trait position could see: the leaf types of its argument type, or every registered projected type and representation."
function _projected_types(@nospecialize(T))
    c = _union_split(Any[T], 32)
    c === nothing || return Any[x[1] for x in c]
    out = Any[]
    for f in (projection, implementation), m in methods(f)
        sig = Base.unwrap_unionall(m.sig)
        length(sig.parameters) == 3 || continue
        p = sig.parameters[3]
        p isa DataType && p <: Type && (U = p.parameters[1]) isa DataType && isconcretetype(U) && U <: T || continue
        any(x -> x === U, out) || push!(out, U)
    end
    return out
end

"Follow an SSA value back through `PiNode`s (the entry's `=== NOTRAIT` check narrows it)."
function _ssa_root(src, @nospecialize(a))
    while a isa Core.SSAValue && src.code[a.id] isa Core.PiNode
        a = src.code[a.id].val
    end
    return a
end

function _scan(mi::Core.MethodInstance, cx::_Walk)
    world = cx.world
    invokes = Tuple{Core.MethodInstance,Bool,Bool}[]
    sites = _Site[]
    m = mi.def
    m isa Method || return _Scan(invokes, sites, false, true)
    res = try
        Base.code_typed_by_type(mi.specTypes; optimize = true, debuginfo = :source, world)
    catch
        nothing
    end
    src = nothing
    if res !== nothing
        for (ci, _) in res
            ci isa Core.CodeInfo || continue
            (ci.parent === nothing || ci.parent.def === m) && (src = ci; break)
        end
    end
    if src === nothing
        push!(sites, _Site(:noscan, false, false, 0, m, mi.specTypes, Core.MethodInstance[], _line(nothing, mi, 0)))
        return _Scan(invokes, sites, false, true)
    end
    sptypes = _CC.sptypes_from_meth_instance(mi)
    succ = _succs(src)
    intry = _intry(src, succ)
    doomed = _doomed(src, succ, intry, c -> _throws_only(cx, c))
    throws = !isempty(doomed) && doomed[1]
    returns = _reaches_return(src, succ)
    site(kind, i, callee, ats, ts = Core.MethodInstance[]) =
        push!(sites, _Site(kind, doomed[i], intry[i], i, callee, ats, ts, _line(src, mi, i)))
    hole(kind, i, callee, ats) = site(kind, i, callee, ats)
    alts = Dict{Int,Vector{Any}}()      # SSA id => the concrete types an entry step can produce
    notrait = false                     # some user type reaching an entry has none of its traits
    for i in eachindex(src.code)
        st = src.code[i]
        rc = _runtime_closure(src, sptypes, st)
        if rc !== nothing
            kind, ats = rc
            if all(_isleaf, ats)
                t = _target_mi(Tuple{ats...}, world)
                site(:root, i, kind, ats, t === nothing ? Core.MethodInstance[] : Core.MethodInstance[t])
            else
                hole(:closure, i, kind, ats)
            end
            Meta.isexpr(st, :invoke) && kind === :task && continue
            Meta.isexpr(st, :foreigncall) && continue
        end
        if Meta.isexpr(st, :invoke)
            c = st.args[1]
            cmi = c isa Core.CodeInstance ? c.def : c
            isdefined(Core, :ABIOverride) && cmi isa Core.ABIOverride && (cmi = cmi.def)
            cmi isa Core.MethodInstance || continue
            cm = cmi.def
            if cm === _enter_method()
                # enter(cache, f, pos, nargs, t): the builder per user type
                a = st.args[3:end]
                cv = _constval(src, sptypes, a[1]); fv = _constval(src, sptypes, a[2])
                pv = _constval(src, sptypes, a[3]); nv = _constval(src, sptypes, a[4])
                T = _argT(src, sptypes, a[5])
                if cv === nothing || fv === nothing || pv === nothing || nv === nothing
                    hole(:trait_arg, i, :enter, Any[T])
                    continue
                end
                cache, f, pos, nargs = something(cv), something(fv), something(pv), something(nv)
                ts = Core.MethodInstance[]
                outs = Any[]
                for U in _projected_types(T)
                    b = Base.invokelatest(_builder, f, pos, nargs, U)
                    if b === NOTRAIT
                        notrait = true
                        continue
                    end
                    t = _target_mi(Tuple{typeof(b),U}, world)
                    t === nothing || push!(ts, t)
                    push!(outs, Base.infer_return_type(b, Tuple{U}))
                    push!(cx.plans, (cache, U, b))
                end
                alts[i] = outs
                site(:trait, i, :enter, Any[T], ts)
                continue
            elseif cm === _enter_callable_method()
                # enter_callable(A, S, spec, f): in a closed world, the function itself
                a = st.args[3:end]
                Av = _constval(src, sptypes, a[1]); Sv = _constval(src, sptypes, a[2])
                Ft = _argT(src, sptypes, a[4])
                c2 = _union_split(Any[Ft], 32)
                if Av === nothing || Sv === nothing || c2 === nothing
                    hole(:trait_arg, i, :enter_callable, Any[Ft])
                    continue
                end
                A, S = something(Av), something(Sv)
                ts = Core.MethodInstance[]
                outs = Any[]
                for x in c2
                    F = x[1]
                    if F <: CObj
                        push!(outs, F)
                    else
                        push!(outs, CObj{A,S,F})
                        t = _target_mi(Tuple{Type{CObj{A,S}},F}, world)
                        t === nothing || push!(ts, t)
                    end
                end
                alts[i] = outs
                site(:trait, i, :callable, Any[Ft], ts)
                continue
            elseif cm isa Method && _machinery_method(cm)
                site(:guard, i, cm.name, Any[])
                continue
            elseif cm isa Method && cm.nospecialize != 0 && isdefined(cm.module, :__tw_entries__)
                # an entry of a trait module: compiled once (that instance must have native code),
                # but analyzed at the call site's argument types, so only the user types the program
                # can pass are enumerated
                ats = Any[_argT(src, sptypes, a) for a in st.args[2:end]]
                vsig = Tuple{ats...}
                if vsig !== cmi.specTypes && vsig <: cmi.specTypes
                    vmi = _view_mi(cm, vsig, world)
                    if vmi !== nothing
                        push!(cx.native_only, cmi)
                        push!(cx.views, vmi)
                        push!(invokes, (vmi, doomed[i], intry[i]))
                        continue
                    end
                end
            end
            push!(invokes, (cmi, doomed[i], intry[i]))
        elseif Meta.isexpr(st, :call)
            cl = _callee(src, sptypes, st.args[1])
            ats = Any[_argT(src, sptypes, a) for a in st.args[2:end]]
            if cl[1] === :const
                f = cl[2]
                if f isa Core.IntrinsicFunction || (f isa Core.Builtin && !_dispatching_builtin(f))
                    continue
                elseif f === Core.finalizer
                    rc === nothing && hole(:closure, i, :finalizer, ats)
                elseif f === checked_call
                    # the entry's call of the worker: one target per combination of what the entry built
                    choices = Vector{Any}[]
                    ok = true
                    for a in st.args[2:end]
                        r = _ssa_root(src, a)
                        if r isa Core.SSAValue && haskey(alts, r.id)
                            push!(choices, alts[r.id])
                        else
                            c3 = _union_split(Any[_argT(src, sptypes, a)], 32)
                            c3 === nothing && (ok = false; break)
                            push!(choices, Any[x[1] for x in c3])
                        end
                    end
                    if !ok
                        hole(:trait_arg, i, f, ats)
                        continue
                    end
                    combos = Vector{Any}[Any[]]
                    for ch in choices
                        combos = Vector{Any}[Any[cmb..., x] for cmb in combos for x in ch]
                    end
                    ts = Core.MethodInstance[]
                    for cmb in combos
                        t = _target_mi(Tuple{typeof(checked_call),cmb...}, world)
                        t === nothing || push!(ts, t)
                    end
                    site(:trait, i, :worker, ats, ts)
                elseif f === fallback
                    notrait ? hole(:fallback, i, f, ats) : site(:trait, i, :fallback, ats)
                elseif f isa Function && parentmodule(f) === TraitWorld && _machinery_method(first(methods(f)))
                    site(:guard, i, f, ats)
                elseif f === Core._apply_iterate
                    g = length(st.args) >= 3 ? _callee(src, sptypes, st.args[3]) : (:unknown, Any)
                    if g[1] === :const && (g[2] isa Core.IntrinsicFunction || (g[2] isa Core.Builtin && !_dispatching_builtin(g[2])))
                        continue
                    end
                    flat = Any[]
                    ok = g[1] === :const
                    for a in st.args[4:end]
                        T = _argT(src, sptypes, a)
                        if T isa DataType && T <: Tuple && (isempty(T.parameters) || !Base.isvarargtype(T.parameters[end]))
                            append!(flat, T.parameters)
                        else
                            ok = false
                        end
                    end
                    ts = ok ? _bounded_targets(g[2], flat, world) : nothing
                    ts === nothing ? hole(:splat, i, g[2], flat) : site(:bounded, i, g[2], flat, ts)
                elseif f isa Core.Builtin
                    hole(f === Core.invokelatest || f === Core.invoke_in_world || f === Core._call_in_world_total ?
                         :latest : :builtin, i, f, ats)
                elseif _is_return_type(f)
                    hole(:inference, i, f, ats)
                elseif rc === nothing
                    ts = _bounded_targets(f, ats, world)
                    ts === nothing ? hole(:dispatch, i, f, ats) : site(:bounded, i, f, ats, ts)
                end
            else
                hole(:callee, i, cl[1] === :field ? string(cl[2], ".", cl[3]) : cl[2], ats)
            end
        elseif Meta.isexpr(st, :foreigncall)
            name = st.args[1]
            name isa QuoteNode && (name = name.value)
            name in _EVAL_CCALLS && hole(:eval, i, name, nothing)
        elseif Meta.isexpr(st, :new_opaque_closure) || Meta.isexpr(st, :cfunction)
            hole(:closure, i, st.head, nothing)
        elseif Meta.isexpr(st, :invoke_modify)
            hole(:builtin, i, :invoke_modify, nothing)
        end
    end
    return _Scan(invokes, sites, throws, returns)
end

function _has_native(mi::Core.MethodInstance, world::UInt)
    isdefined(mi, :cache) || return false
    ci = mi.cache
    while true
        ci.owner === nothing && _isvalid(ci, world) && ci.invoke != C_NULL && return true
        isdefined(ci, :next) || return false
        ci = ci.next
    end
end

# reach levels: an error path, a normal path, a normal path inside a `try`
# (where even a throw is followed by more execution)
const _ERR, _NORMAL, _PROTECTED = 0x00, 0x01, 0x02
_sublevel(lv::UInt8, doomed::Bool, intry::Bool) =
    lv == _PROTECTED ? _PROTECTED : lv == _ERR ? _ERR : intry ? _PROTECTED : doomed ? _ERR : _NORMAL

"""
    verify_main(f, argtypes::Tuple = (); compile = false, entrypoints = false) -> MainReport

Check that calling `f` with arguments of types `argtypes` can only reach
compiled code: every dynamic call has finitely many targets known now, or is
one of TraitWorld's entry steps, whose targets are enumerated from the
argument types and the registered projections. Runs the build-time checks of
every enumerated worker (rules 1 and 3, the piracy audit) and reports the
holes, separating those reached only on the way to an uncaught `throw`.

`compile = true` compiles every target. `entrypoints = true` registers them
with `Base.Experimental.entrypoint` for `juliac --trim`; in a trimmed build it
also closes the world: entry caches are filled now, and the checks, the guard,
erasure and reflection are switched off in the binary.
"""
function verify_main(@nospecialize(f), @nospecialize(argtypes::Tuple = ()); compile::Bool = false, entrypoints::Bool = false)
    world = Base.get_world_counter()
    cx = _Walk(world)
    entry = Base.signature_type(f, argtypes)
    root = _target_mi(entry, world)
    root === nothing && error("verify_main: no method for $entry")
    level = IdDict{Core.MethodInstance,UInt8}()
    work = Tuple{Core.MethodInstance,UInt8}[(root, _NORMAL)]
    while !isempty(work)
        mi, lv = pop!(work)
        old = get(level, mi, nothing)
        old !== nothing && old >= lv && continue
        level[mi] = lv
        sc = _get_scan(cx, mi)
        sc === nothing && continue
        for (c, d, t) in sc.invokes
            push!(work, (c, _sublevel(lv, d, t)))
        end
        for s in sc.sites, t in s.targets
            push!(work, (t, _sublevel(lv, s.doomed, s.intry)))
        end
    end
    static_calls = bounded = trait_sites = guard_sites = roots = 0
    holes = Hole[]
    targets = Pair{Symbol,Any}[]
    tseen = Base.IdSet{Any}()
    dyn_roots = Base.IdSet{Any}()
    for (mi, lv) in level
        sc = cx.scans[mi]
        static_calls += length(sc.invokes)
        for s in sc.sites
            if s.kind === :bounded || s.kind === :root
                s.kind === :bounded ? (bounded += 1) : (roots += 1)
                for t in s.targets
                    push!(dyn_roots, t.specTypes)
                end
            elseif s.kind === :trait
                trait_sites += 1
                for t in s.targets
                    t in tseen && continue
                    push!(tseen, t)
                    push!(targets, (s.callee isa Symbol ? s.callee : :trait) => t.specTypes)
                end
            elseif s.kind === :guard
                guard_sites += 1
            else
                ep = _sublevel(lv, s.doomed, s.intry) == _ERR
                push!(holes, Hole(s.kind, ep, mi, s.stmt, s.callee, s.argtypes, s.line))
            end
        end
    end
    sort!(holes; by = h -> (h.errorpath, string(h.kind), string(h.callee)))
    # build-time checks of every enumerated worker: rules 1 and 3, and the piracy audit
    findings = Pair{Any,Vector{PiracyFinding}}[]
    problems = String[]
    for (kind, S) in targets
        kind === :worker || continue
        W = Tuple{S.parameters[2:end]...}
        append!(problems, worker_problems(W))
        fs = audit(W; compile = false)
        isempty(fs) || push!(findings, W => fs)
    end
    unique!(problems)
    allroots = Any[entry; [S for (_, S) in targets]; collect(dyn_roots); [mi.specTypes for mi in cx.native_only]]
    if compile
        for S in allroots
            ccall(:jl_compile_hint, Int32, (Any,), S)
        end
    end
    if entrypoints
        for S in allroots
            Base.Experimental.entrypoint(S)
        end
        if Base.JLOptions().trim != 0
            close_world!(cx.plans)
        end
    end
    generating = ccall(:jl_generating_output, Cint, ()) == 1
    uncompiled = Any[]
    if !generating
        for (mi, lv) in level
            mi in cx.views && continue
            lv != _ERR && !_has_native(mi, Base.get_world_counter()) && push!(uncompiled, mi.specTypes)
        end
        for mi in cx.native_only
            _has_native(mi, Base.get_world_counter()) || push!(uncompiled, mi.specTypes)
        end
    end
    return MainReport(entry, length(level), count(!=(_ERR), values(level)), static_calls, bounded,
                      trait_sites, targets, roots, guard_sites, holes, uncompiled, !generating, findings, problems)
end

"""
Close the world for a trimmed binary: fill the entry caches with every builder
the program can need, and switch off what needs the compiler or reflection
(the checks ran at build time; no method can be added to a binary).
"""
function close_world!(plans)
    for (cache, U, b) in plans
        cache.builders[U] = b
    end
    CLOSED_WORLD[] = true
    MODE[] = :recompile
    return nothing
end

function Base.show(io::IO, ::MIME"text/plain", r::MainReport)
    nh = count(h -> !h.errorpath, r.holes)
    ne = length(r.holes) - nh
    verdict = isclosed(r) ? "CLOSED: every call on a normal path reaches enumerated, compiled code" :
              nh > 0 ? "OPEN: $nh dynamic call(s) on normal paths need targets nobody enumerated" :
              "OPEN: $(length(r.uncompiled)) method instance(s) on normal paths lack native code"
    println(io, "verify_main ", r.entry, "\n  ", verdict)
    println(io, "  closure: ", r.reached, " method instances (", r.normal, " on normal paths), ",
            r.static_calls, " static calls")
    kinds = Dict{Symbol,Int}()
    for (k, _) in r.targets; kinds[k] = get(kinds, k, 0) + 1; end
    println(io, "  dynamic calls: ", r.bounded, " bounded; ", r.trait_sites, " trait dispatch sites -> ",
            length(r.targets), " targets (", join(("$v $k" for (k, v) in sort!(collect(kinds))), ", "),
            "); ", r.roots, " runtime closure roots; ", r.guard_sites, " guard")
    groups = Dict{Tuple{Bool,Symbol,String},Vector{Hole}}()
    for h in r.holes
        push!(get!(groups, (h.errorpath, h.kind, _calleestr(h)), Hole[]), h)
    end
    for ep in (false, true)
        ks = sort!([k for k in keys(groups) if k[1] == ep]; by = k -> (-length(groups[k]), k[2], k[3]))
        n = ep ? ne : nh
        println(io, ep ? "  holes on uncaught-error paths only: " : "  holes on normal paths: ", n,
                n > 0 ? " (" * string(length(ks)) * " distinct)" : "")
        lim = ep ? 8 : 25
        for k in first(ks, lim)
            hs = groups[k]
            h = first(hs)
            println(io, "    ", rpad(string(k[2]), 10), rpad(k[3], 60), " ×", length(hs), "  ", h.line)
        end
        length(ks) > lim && println(io, "    … ", length(ks) - lim, " more")
    end
    if r.checked_native
        println(io, "  normal-path method instances without native code: ", length(r.uncompiled))
        for S in first(r.uncompiled, 10)
            println(io, "    ", S)
        end
        length(r.uncompiled) > 10 && println(io, "    … ", length(r.uncompiled) - 10, " more")
    else
        println(io, "  native code: not checked (generating a package image)")
    end
    println(io, "  build-time checks of enumerated workers (rules 1 and 3): ",
            isempty(r.problems) ? "clean" : string(length(r.problems)) * " problem(s)")
    for p in first(r.problems, 10)
        println(io, "    ", p)
    end
    print(io, "  build-time piracy audit of enumerated workers: ",
          isempty(r.findings) ? "clean" : string(sum(length ∘ last, r.findings)) * " finding(s)")
end

function _calleestr(h::Hole)
    c = h.callee
    s = c isa Function ? string(nameof(c)) : string(c)
    h.argtypes isa Vector || return s
    return s * "(" * join(("::" * string(T) for T in h.argtypes), ", ") * ")"
end

