# Concreteness and fully typed mode (traits §14; lowering §14; compiler §2.7).
#
# Fully typed code: every call in it, and in what it calls, has known argument types, so code
# compiled by facts infers it as plain code does. `fully_typed(f, argtypes)` walks the code, inferred
# by facts at each signature it reaches, and reports each call dispatched when it runs on a normal
# path, with its root cause. The modes `@warn_not_fully_typed` and `@enforce_fully_typed` are the
# compiler's (compiler §2.7): code that fails them starts with a check that calls this library's hook.

const CC = Base.Compiler

"A call in the code that is dispatched when it runs (a run-time site), with its root cause."
struct RuntimeSite
    kind::Symbol            # :dispatch, :callee, :splat, :latest, :barrier
    code::Any               # the MethodInstance whose code holds it
    file::Symbol
    line::Int
    call::String            # the call, at the types inference knows
    cause::Vector{String}   # from the call to its root cause, last
end

"""
    FullyTypedReport

What `fully_typed` found: the calls dispatched when they run on normal paths (none for fully typed
code), the entry's result type and, where it is abstract, its root cause.
"""
struct FullyTypedReport
    sig::Any
    sites::Vector{RuntimeSite}
    result::Any
    result_cause::Vector{String}
    complete::Bool          # false where the walk stopped at its bound
end

"Whether the code `fully_typed` checked is fully typed: no call on a normal path dispatched when it runs."
isfullytyped(r::FullyTypedReport) = isempty(r.sites)

"""
    fully_typed(f, argtypes) -> FullyTypedReport

The calls in `f` at `argtypes`, and in what it calls, that are dispatched when they run, each with its
root cause, through any number of layers (traits §14). Error paths are left out. Operations on a value
the code knows only by its trait count as declared.
"""
fully_typed(@nospecialize(f), @nospecialize(argtypes::Tuple)) =
    fully_typed_by_type(Base.signature_type(f, argtypes))
fully_typed(@nospecialize(f), @nospecialize(argtypes::Type{<:Tuple})) = fully_typed(f, Tuple(argtypes.parameters))

const _WALK_BOUND = 400
# `verify_main` walks a whole program
const _VERIFY_BOUND = 100_000

function fully_typed_by_type(@nospecialize(sig); world::UInt = Base.get_world_counter())
    w = _walk(sig, world)
    return FullyTypedReport(sig, w.sites, w.result, w.result_cause, w.complete)
end

# the walk shared by `fully_typed` and `verify_main`: every signature the code reaches on normal
# paths, inferred by facts, its run-time sites, and the targets beyond the calls it resolves
function _walk(@nospecialize(sig), world::UInt; bound::Int = _WALK_BOUND)
    interp = CC.NativeInterpreter(world; facts = true)
    sites = RuntimeSite[]
    seen = Any[]
    queue = Any[sig]
    extra = Any[]
    result, result_cause = Any, String[]
    complete = true
    first = true
    while !isempty(queue)
        T = popfirst!(queue)
        T in seen && continue
        push!(seen, T)
        if length(seen) > bound
            complete = false
            break
        end
        got = _ircode(T, interp, world)
        got === nothing && continue
        ir, rt, mi = got
        if first
            result = rt
            ft_abstract(rt) && (result_cause = _return_cause(ir, mi, interp, world, 0))
            first = false
        end
        _module_of(mi) === (@__MODULE__) && continue        # the library's own machinery
        _scan!(sites, queue, extra, ir, mi, interp, world)
    end
    return (; sites, seen, extra, result, result_cause, complete)
end

function _ircode(@nospecialize(T), interp, world)
    res = try
        Base.code_ircode_by_type(T; world, interp, optimize_until = "CC: COMPACT_1")
    catch
        return nothing
    end
    length(res) == 1 || return nothing
    ir, rt = res[1]
    ms = Base._methods_by_ftype(T, 1, world)
    (ms isa Vector && length(ms) == 1) || return nothing
    mi = CC.specialize_method(ms[1]::Core.MethodMatch)
    return ir, rt, mi
end

_module_of(mi::Core.MethodInstance) = mi.def isa Method ? (mi.def::Method).module : mi.def

"Whether a type fails fully typed mode as a value's type: as the compiler's rule (compiler §2.7)."
# whether a result's type is abstract in the report's sense: neither concrete, a union of at most four
# concrete types, a type's type, nor a trait or an intersection of traits. The report names its cause.
function ft_abstract(@nospecialize(rt))
    rt = CC.widenconst(rt)
    (rt === Union{} || isconcretetype(rt) || CC.isType(rt)) && return false
    if rt isa Union
        ts = Base.uniontypes(rt)
        length(ts) <= 4 && all(t -> isconcretetype(t) || CC.isType(t), ts) && return false
    end
    ccall(:jl_is_trait_arg_type, Cint, (Any,), rt) != 0 && return false
    return true
end

# the blocks on a normal path: those from which a return with a value is reachable
function _normal_blocks(ir)
    cfg = ir.cfg
    n = length(cfg.blocks)::Int    # `ir` is untyped: a range of an untyped length reaches Base's promotion (E-307)
    ok = falses(n)
    work = Int[]
    for b in 1:n
        last = ir.stmts[cfg.blocks[b].stmts[end]][:stmt]
        if last isa Core.ReturnNode && isdefined(last, :val)
            ok[b] = true
            push!(work, b)
        end
    end
    while !isempty(work)
        b = pop!(work)
        for p in cfg.blocks[b].preds
            (p >= 1 && !ok[p]) || continue
            ok[p] = true
            push!(work, p)
        end
    end
    return ok
end

function _scan!(sites, queue, extra, ir, mi, interp, world)
    normal = _normal_blocks(ir)
    for i in 1:(length(ir.stmts)::Int)
        normal[CC.block_for_inst(ir.cfg, i)] || continue
        inst = ir.stmts[i]
        stmt = inst[:stmt]
        Meta.isexpr(stmt, :call) || continue
        info = inst[:info]
        ft = CC.widenconst(CC.argextype(stmt.args[1], ir))
        f = CC.singleton_type(CC.argextype(stmt.args[1], ir))
        kind = _site_kind(info, f, ft)
        if kind === :resolved
            for T in _callee_sigs(info)
                push!(queue, T)
            end
            _callable_targets!(extra, queue, info, ir, stmt)
        elseif kind === :none
            _operation_targets!(extra, queue, info, ir, stmt, f)
        elseif kind === :dispatch && _cast_targets!(extra, queue, ir, stmt, f)
            # a cast on a value known only by its trait: the declared members are its targets
        else
            push!(sites, _site(kind, ir, mi, i, stmt, interp, world))
        end
    end
end

# the trait a `compiled_for` cast's operand is known by, where `a` is such a cast's result
function _cast_trait(ir, @nospecialize(a))
    a isa Core.SSAValue || return nothing
    stmt = ir.stmts[a.id][:stmt]
    (Meta.isexpr(stmt, :call) && length(stmt.args) == 2) || return nothing
    CC.singleton_type(CC.argextype(stmt.args[1], ir)) === Core._cast_compiled || return nothing
    X = CC.widenconst(CC.argextype(stmt.args[2], ir))
    return _is_trait_arg(X) ? X : nothing
end

# a call with `compiled_for` on a value known only by its trait: the callee at each declared member
# (traits §16). True where the statement is such a call, or the cast itself, with its targets listed.
function _cast_targets!(extra, queue, ir, stmt, @nospecialize(f))
    args = (stmt::Expr).args
    if f === Core._cast_compiled
        (length(args) == 2 && _is_trait_arg(CC.widenconst(CC.argextype(args[2], ir)))) || return false
        T = Tuple{typeof(Core._cast_compiled), Any}
        T in extra || (push!(extra, T); push!(queue, T))
        return true
    end
    (f === Core.attributed_call && length(args) >= 3) || return false
    g = CC.singleton_type(CC.argextype(args[3], ir))
    g === nothing && return false
    choices = Vector{Any}[]
    cast = false
    for a in args[4:end]
        X = _cast_trait(ir, a)
        if X === nothing
            t = CC.widenconst(CC.argextype(a, ir))
            ft_abstract(t) && return false
            push!(choices, Any[t])
        else
            ms = Any[M for M in members_of(X) if M isa DataType && isconcretetype(M)]
            isempty(ms) && return false
            push!(choices, ms)
            cast = true
        end
    end
    cast || return false
    attr = CC.argextype(args[2], ir)
    bits = attr isa CC.Const && attr.val isa Int ? reinterpret(UInt64, attr.val) : UInt64(0)
    mask = bits % UInt32
    dyn = (bits >> 32) % UInt32 & mask
    world = Base.get_world_counter()
    for ts in Iterators.product(choices...)
        T = Tuple{Core.Typeof(g), ts...}
        T in extra || (push!(extra, T); push!(queue, T))
        # the instance the cast runs: compiled with the call's attributes (compiler §6.3)
        mask == 0 && continue
        mi = ccall(:jl_attributed_mi, Any, (Any, UInt32, UInt32, UInt), T, mask, dyn, world)
        mi isa Core.MethodInstance && !(mi in extra) && push!(extra, mi)
    end
    return true
end

# a function passed at a `Callable{A, S}` argument: one target at its signature (traits §16)
function _callable_targets!(extra, queue, @nospecialize(info), ir, stmt)
    while info isa CC.AttributedCallInfo
        info = info.info
    end
    info isa CC.ConstCallInfo && (info = info.call)
    (info isa CC.MethodMatchInfo || info isa CC.UnionSplitInfo) || return
    argtypes = Any[CC.widenconst(CC.argextype(a, ir)) for a in stmt.args]
    for k in 1:CC.nsplit(info), mm in CC.getsplit(info, k).matches
        sig = Base.unwrap_unionall((mm::Core.MethodMatch).method.sig)
        sig isa DataType || continue
        for (i, d) in enumerate(sig.parameters)
            (i <= length(argtypes) && d isa Type && !(d isa TypeVar)) || continue
            dd = Base.unwrap_unionall(d)
            (dd isa DataType && dd.name === Base.unwrap_unionall(Core.Callable).name) || continue
            F = argtypes[i]
            (isconcretetype(F) && !(F <: Dynamic)) || continue
            A = dd.parameters[1]
            (A isa Type && A <: Tuple && !Base.has_free_typevars(A)) || continue
            T = Tuple{F, A.parameters...}
            T in extra || (push!(extra, T); push!(queue, T))
        end
    end
end

# an operation on a value known only by its trait: a target at each declared member (traits §16)
function _operation_targets!(extra, queue, @nospecialize(info), ir, stmt, @nospecialize(f))
    (info isa CC.DeclaredResultInfo || info isa CC.SplitCallInfo) || return
    f === nothing && return
    argtypes = Any[CC.widenconst(CC.argextype(a, ir)) for a in (stmt::Expr).args[2:end]]
    k = findfirst(_is_trait_arg, argtypes)
    k === nothing && return
    X = argtypes[k]
    for M in members_of(X)
        M isa DataType && isconcretetype(M) || continue
        ts = copy(argtypes)
        ts[k] = M
        T = Tuple{Core.Typeof(f), ts...}
        T in extra || (push!(extra, T); push!(queue, T))
    end
end

# what a call statement is: :none (a builtin or a declared operation), :resolved (inferred, with its
# callees), or the kind of run-time site
function _site_kind(@nospecialize(info), @nospecialize(f), @nospecialize(ft))
    dispatch = false
    while true
        if info isa CC.AttributedCallInfo
            dispatch |= info.dispatch
            info = info.info
        else
            break
        end
    end
    dispatch && return :barrier
    (info isa CC.DeclaredResultInfo || info isa CC.SplitCallInfo || info isa CC.KeepInfo) && return :none
    if f isa Core.Builtin
        if f === Core._apply_iterate
            return info isa CC.NoCallInfo ? :splat : :resolved
        elseif f === Core._call_latest || f === Core.invoke_in_world
            return :latest
        elseif f === Core.invoke
            return info isa CC.InvokeCallInfo ? :resolved : :dispatch
        elseif f === Core.attributed_call
            return info isa CC.NoCallInfo ? :dispatch : :resolved
        end
        return :none
    end
    f === nothing && !(ft <: Core.Builtin) && return :callee
    info isa CC.NoCallInfo && return :dispatch
    return :resolved
end

# the signatures a resolved call's callees are inferred at
function _callee_sigs(@nospecialize(info))
    out = Any[]
    while info isa CC.AttributedCallInfo
        info = info.info
    end
    if info isa CC.ApplyCallInfo
        info = info.call
    end
    if info isa CC.InvokeCallInfo
        push!(out, CC.specialize_method(info.match).specTypes)
        return out
    end
    (info isa CC.MethodMatchInfo || info isa CC.UnionSplitInfo || info isa CC.ConstCallInfo) || return out
    for k in 1:CC.nsplit(info)
        r = CC.getsplit(info, k)
        for m in r.matches
            push!(out, CC.specialize_method(m::Core.MethodMatch).specTypes)
        end
    end
    return out
end

function _lineof(ir, mi, i)
    lis = try Base.IRShow.buildLineInfoNode(ir.debuginfo, mi, i) catch; Any[] end
    isempty(lis) && return (Symbol("?"), 0)
    li = lis[end]
    return (Symbol(li.file), Int(li.line))
end

# a type as its own module names it (`Holder`, not `Main.M.Holder`)
_tstr(@nospecialize(T)) = sprint(show, T; context = :module => _home(T))
function _home(@nospecialize(T))
    S = Base.unwrap_unionall(T)
    S isa DataType || return Main
    m = Base.moduleroot(S.name.module)
    return m === Core || m === Base ? Main : S.name.module
end

function _site(kind::Symbol, ir, mi, i, stmt, interp, world)
    file, line = _lineof(ir, mi, i)
    args = (stmt::Expr).args
    types = Any[CC.widenconst(CC.argextype(a, ir)) for a in args]
    fname = let f = CC.singleton_type(CC.argextype(args[1], ir))
        f === nothing ? "(::" * _tstr(types[1]) * ")" : sprint(show, f)
    end
    call = fname * "(" * join(("::" * _tstr(t) for t in types[2:end]), ", ") * ")"
    cause = String[]
    if kind === :callee
        push!(cause, "the function called is a value of type " * _tstr(types[1]) * ", not known when compiled")
        append!(cause, _origin(ir, mi, args[1], interp, world, 0))
    elseif kind === :splat
        push!(cause, "a splat of a collection whose length is not known when compiled")
    elseif kind === :latest
        push!(cause, "a call in the latest world, which is not known when compiled")
    elseif kind === :barrier
        push!(cause, "an argument compiled for its value's type, which the caller does not know (a function barrier)")
    end
    for k in 2:length(args)
        (kind === :dispatch || kind === :barrier) || break
        ft_abstract(types[k]) || continue
        k == 2 && kind === :barrier && continue
        push!(cause, "argument $(k - 1) is " * _tstr(types[k]))
        append!(cause, _origin(ir, mi, args[k], interp, world, 0))
        break
    end
    isempty(cause) && push!(cause, "its argument types are not known when compiled")
    return RuntimeSite(kind, mi, file, line, call, cause)
end

# where a value of an abstract type comes from, in the code's own terms
function _origin(ir, mi, @nospecialize(v), interp, world, depth::Int)
    out = String[]
    depth > 6 && return out
    if v isa Core.Argument
        m = mi.def
        names = m isa Method ? Base.method_argnames(m) : Symbol[]
        nm = v.n <= length(names) ? names[v.n] : Symbol("#", v.n)
        push!(out, "the argument `$nm` is " * _tstr(CC.widenconst(CC.argextype(v, ir))))
    elseif v isa GlobalRef
        push!(out, isconst(v.mod, v.name) ? "the global `$(v.mod).$(v.name)`" :
                   "the global `$(v.mod).$(v.name)`, which is not constant")
    elseif v isa Core.SSAValue
        inst = ir.stmts[v.id]
        stmt = inst[:stmt]
        T = CC.widenconst(inst[:type])
        if stmt isa Core.PhiNode
            ts = unique!(Any[CC.widenconst(CC.argextype(stmt.values[k], ir)) for k in 1:length(stmt.values) if isassigned(stmt.values, k)])
            push!(out, "a variable whose type differs between paths: " * join(map(_tstr, ts), ", "))
        elseif Meta.isexpr(stmt, :call)
            f = CC.singleton_type(CC.argextype(stmt.args[1], ir))
            info = inst[:info]
            while info isa CC.AttributedCallInfo
                info = info.info
            end
            if (f === getfield || f === getproperty) && length(stmt.args) >= 3
                O = CC.widenconst(CC.argextype(stmt.args[2], ir))
                name = CC.argextype(stmt.args[3], ir)
                name = name isa Core.Const ? name.val : nothing
                if name isa Symbol
                    push!(out, _field_cause(O, name, T))
                else
                    push!(out, "a field of " * _tstr(O) * ", read by a name not known when compiled")
                end
            elseif f === getindex && length(stmt.args) >= 2 &&
                   CC.widenconst(CC.argextype(stmt.args[2], ir)) <: Union{AbstractArray, AbstractDict}
                A = CC.widenconst(CC.argextype(stmt.args[2], ir))
                push!(out, "an element of " * _tstr(A) * ", whose element type is " * _tstr(eltype(A)))
            elseif info isa CC.DeclaredResultInfo || info isa CC.SplitCallInfo
                push!(out, "the result of `$(f)`, an operation declared to return " * _tstr(T))
            elseif info isa CC.NoCallInfo
                push!(out, "the result of a call dispatched when it runs: `$(f === nothing ? "?" : f)(…)` is " * _tstr(T))
            else
                sigs = _callee_sigs(info)
                push!(out, "`$(f === nothing ? "?" : f)` returns " * _tstr(T) * (length(sigs) == 1 ? " at " * _tstr(sigs[1]) : ""))
                if length(sigs) == 1 && depth < 3
                    got = _ircode(sigs[1], interp, world)
                    got === nothing || append!(out, _return_cause(got[1], got[3], interp, world, depth + 1))
                end
            end
        elseif Meta.isexpr(stmt, :new)
            push!(out, "a new " * _tstr(T))
        else
            push!(out, "a value of type " * _tstr(T))
        end
    end
    return out
end

# the root cause of an abstract result: the first returned value of an abstract type
function _return_cause(ir, mi, interp, world, depth::Int)
    for i in 1:(length(ir.stmts)::Int)
        st = ir.stmts[i][:stmt]
        st isa Core.ReturnNode && isdefined(st, :val) || continue
        ft_abstract(CC.argextype(st.val, ir)) || continue
        return _origin(ir, mi, st.val, interp, world, depth)
    end
    return String[]
end

function _field_cause(@nospecialize(O), name::Symbol, @nospecialize(T))
    if _is_trait_arg(O)
        return "field `$name` of `$(_tstr(O))` is declared " * _tstr(T)
    elseif O isa DataType && isconcretetype(O) && hasfield(O, name)
        return "field `$name` of `$(_tstr(O))` is declared " * _tstr(fieldtype(O, name))
    end
    return "field `$name` of a value of type " * _tstr(O)
end

const _KIND_HINT = Dict(
    :dispatch => "give the values concrete types (a typed field or container, a function barrier), or type them by a trait that declares the result",
    :callee   => "pass the function as a `Callable{A, S}`, or store it with a concrete type",
    :splat    => "pass a tuple, or the elements",
    :latest   => "a call in the latest world (`invokelatest`) is never fully typed",
    :barrier  => "the caller does not know the argument's type: type it, or make the argument `Dynamic`",
)

function Base.show(io::IO, ::MIME"text/plain", r::FullyTypedReport)
    if isfullytyped(r)
        print(io, "fully typed: ", r.sig)
    else
        n = length(r.sites)
        print(io, "not fully typed: ", r.sig, "\n  ", n, n == 1 ? " call is" : " calls are",
              " dispatched when ", n == 1 ? "it runs" : "they run", ":")
        for s in first(r.sites, 12)
            print(io, "\n  ", s.file, ":", s.line, "  ", s.call)
            for (k, c) in enumerate(s.cause)
                print(io, "\n      ", k == 1 ? "" : "← ", c)
            end
            print(io, "\n      (", _KIND_HINT[s.kind], ")")
        end
        n > 12 && print(io, "\n  … ", n - 12, " more")
    end
    if !isempty(r.result_cause)
        print(io, "\n  the result is ", _tstr(r.result), ": ", join(r.result_cause, " ← "))
    end
    r.complete || print(io, "\n  (the walk stopped after $(_WALK_BOUND) signatures)")
end
Base.show(io::IO, r::FullyTypedReport) =
    print(io, isfullytyped(r) ? "FullyTypedReport(fully typed)" : "FullyTypedReport($(length(r.sites)) run-time sites)")

"""
    NotFullyTypedError

Raised under `@enforce_fully_typed` by code that has a call it cannot resolve when compiled, in it or
in what it calls (traits §14).
"""
struct NotFullyTypedError <: Exception
    sig::Any
    report::Union{Nothing,FullyTypedReport}
end
function Base.showerror(io::IO, e::NotFullyTypedError)
    print(io, "NotFullyTypedError: ")
    e.report === nothing ? print(io, "not fully typed: ", e.sig) : show(io, MIME"text/plain"(), e.report)
end

"""
    AbstractTypeError

Raised by a method under `@enforce_concrete_only result` at a signature whose result is not concrete
(traits §14).
"""
struct AbstractTypeError <: Exception
    sig::Any
    result::Any
    report::Union{Nothing,FullyTypedReport}
end
function Base.showerror(io::IO, e::AbstractTypeError)
    print(io, "AbstractTypeError: ", e.sig, " returns a value of the abstract type ", _tstr(e.result))
    if e.report !== nothing && !isempty(e.report.result_cause)
        print(io, "\n  ", join(e.report.result_cause, "\n  ← "))
    end
end

# the compiler's check calls this with svec(mi, level, warned, kind, rt) (compiler §2.7)
const _FT_ERRORS = IdDict{Any,Any}()
function _fully_typed_hook(site::Core.SimpleVector)
    mi = site[1]::Core.MethodInstance
    level = site[2]::Int
    err = get!(_FT_ERRORS, mi) do
        r = try
            fully_typed_by_type(mi.specTypes)
        catch
            nothing
        end
        NotFullyTypedError(mi.specTypes, r)
    end
    level == 2 && throw(err)
    @warn "@warn_not_fully_typed: " * sprint(showerror, err)
    return nothing
end

"""
    @enforce_fully_typed f(…) = …
    @enforce_fully_typed @trait_module

Fully typed mode with errors (traits §14): the method (or every method of the module) is compiled by
facts; where its code at a signature has a call it cannot resolve when compiled, in it or in what it
calls, the code raises `NotFullyTypedError`. The result's type is no fault: a type is a fault where it
is used (`@enforce_concrete_only result` asks for a concrete result). Fully typed code pays nothing.
"""
macro enforce_fully_typed(ex)
    esc(_fully_typed_mode(__module__, ex, :enforce))
end

"""
    @warn_not_fully_typed f(…) = …
    @warn_not_fully_typed @trait_module

Fully typed mode with warnings (traits §14): as `@enforce_fully_typed`, but the code warns at its
first run at a signature, with `fully_typed`'s report, and runs.
"""
macro warn_not_fully_typed(ex)
    esc(_fully_typed_mode(__module__, ex, :warn))
end

function _fully_typed_mode(mod::Module, ex, level::Symbol)
    if Meta.isexpr(ex, :macrocall) && _macro_name(ex.args[1]) === Symbol("@trait_module")
        return Expr(:macrocall, ex.args..., Expr(:(=), :fully_typed, QuoteNode(level)))
    end
    def = Meta.isexpr(ex, :macrocall) ? macroexpand(mod, ex) : ex
    _is_definition(def) || error("@$(level === :enforce ? "enforce_fully_typed" : "warn_not_fully_typed") " *
                                 "applies to a method's definition or to @trait_module")
    return Base.pushmeta!(def, level === :enforce ? :fully_typed_enforce : :fully_typed_warn)
end

_macro_name(@nospecialize(h)) = h isa Symbol ? h : h isa GlobalRef ? h.name :
    (Meta.isexpr(h, :.) && h.args[end] isa QuoteNode) ? h.args[end].value : h

function _is_definition(@nospecialize(ex))
    Meta.isexpr(ex, :function) && return true
    Meta.isexpr(ex, :(=)) || return false
    lhs = ex.args[1]
    while Meta.isexpr(lhs, :where) || Meta.isexpr(lhs, :(::))
        lhs = lhs.args[1]
    end
    return Meta.isexpr(lhs, :call)
end

# ---------------------------------------------------------------------------------------------
# Concrete parts (traits §14): a membership's or a call's named parts are concrete.

"""
Whether `v` is concrete in the sense of traits §14: a concrete type whose parameters are concrete in
the same sense, or a `Union` of at most four such types; a value that is not a type; a `Dynamic{X}`;
a trait as a parameter's value.
"""
function is_concrete_part(@nospecialize(v))
    v isa Type || return true
    if v isa Union
        ts = Base.uniontypes(v)
        return length(ts) <= 4 && all(is_concrete_part, ts)
    end
    v isa DataType || return false
    _is_trait_arg(v) && return true
    v <: Dynamic && return true
    isconcretetype(v) || return false
    for p in v.parameters
        p isa TypeVar && return false
        Base.isvarargtype(p) && return false
        is_concrete_part(p) || return false
    end
    return true
end

"Whether `T` is concrete (§14), as a constant where the call is compiled."
@generated _concrete_known(::Type{T}) where {T} = is_concrete_part(T)

const _CONCRETE_WARNED = Set{Any}()

@noinline function _concrete_fail(level::Symbol, @nospecialize(f), n::Symbol, @nospecialize(T), what::String)
    tag = level === :enforce ? "@enforce_concrete_only" : "@warn_on_abstract"
    msg = "`$f`: $what is $T, which is not concrete (`$tag $n`)"
    level === :enforce && throw(TraitUseError(msg))
    key = (f, n, T)
    key in _CONCRETE_WARNED && return nothing
    push!(_CONCRETE_WARNED, key)
    @warn msg * "; the code for it dispatches when it runs where it uses that type"
    return nothing
end

# the method's result at the signature: the type inference gives it, known where the call is compiled
@inline _concrete_result(level::Symbol, @nospecialize(f), ::Type{T}) where {T} =
    _concrete_known(T) ? nothing : _result_fail(level, f, T)
@noinline function _result_fail(level::Symbol, @nospecialize(f), @nospecialize(T))
    level === :enforce && throw(AbstractTypeError(f, T, nothing))
    key = (f, :result, T)
    key in _CONCRETE_WARNED && return nothing
    push!(_CONCRETE_WARNED, key)
    @warn "`$f` returns a value of the type $T, which is not concrete (`@warn_on_abstract result`)"
    return nothing
end

# a `where` variable a trait fixes, at the call: decided where the call is compiled
@inline _concrete_param(level::Symbol, @nospecialize(f), n::Symbol, ::Type{T}) where {T} =
    _concrete_known(T) ? nothing : _concrete_fail(level, f, n, T, "`$n`")
@inline _concrete_param(level::Symbol, @nospecialize(f), n::Symbol, @nospecialize(v)) = nothing
# a trait argument's Self: its value's type where the instance is compiled for it; a `Dynamic` is not checked
@inline _concrete_self(level::Symbol, @nospecialize(f), n::Symbol, ::Dynamic) = nothing
@inline _concrete_self(level::Symbol, @nospecialize(f), n::Symbol, x::T) where {T} =
    _concrete_known(T) ? nothing : _concrete_fail(level, f, n, T, "the argument `$n`'s type")

"""
    @enforce_concrete_only names… f(…) = …
    @warn_on_abstract names… f(…) = …

Before a method: a call where a named part is not concrete (traits §14) raises `TraitUseError`, or
warns once per method and type. The names are the method's `where` variables and its trait arguments,
each standing for its `Self`. Without names, all of them. `result` names the method's result: a
signature at which inference gives it a type that is not concrete raises `AbstractTypeError`. In a trait's body, the same macros name the
trait's parameters and `Self`, checked at each membership.
"""
macro enforce_concrete_only(args...)
    esc(_concrete_method(__module__, args, :enforce))
end
"
    @warn_on_abstract names… f(…) = …

As `@enforce_concrete_only`, with a warning once per method and type instead of an error (traits §14).
"
macro warn_on_abstract(args...)
    esc(_concrete_method(__module__, args, :warn))
end

function _concrete_method(mod::Module, args, level::Symbol)
    isempty(args) && error("@enforce_concrete_only and @warn_on_abstract go before a method, or in a trait's body")
    def = args[end]
    def = Meta.isexpr(def, :macrocall) ? macroexpand(mod, def) : def
    _is_definition(def) || error("@enforce_concrete_only and @warn_on_abstract go before a method's definition, or in a trait's body")
    names = Symbol[a for a in args[1:end-1]]
    sig = def.args[1]
    wherevars = Symbol[]
    while Meta.isexpr(sig, :where)
        for w in sig.args[2:end]
            push!(wherevars, w isa Symbol ? w : (w.args[1])::Symbol)
        end
        sig = sig.args[1]
    end
    Meta.isexpr(sig, :(::)) && (sig = sig.args[1])
    call = sig::Expr
    fname = call.args[1]
    argnames = Symbol[]
    for a in call.args[2:end]
        Meta.isexpr(a, :parameters) && continue
        a = Meta.isexpr(a, :kw) ? a.args[1] : a
        Meta.isexpr(a, :(::)) && length(a.args) == 2 && a.args[1] isa Symbol && push!(argnames, a.args[1])
    end
    isempty(names) && (names = vcat(wherevars, argnames))
    lib = GlobalRef(@__MODULE__, :_concrete_param)
    libself = GlobalRef(@__MODULE__, :_concrete_self)
    checks = Any[]
    for n in names
        if n in wherevars
            push!(checks, :($lib($(QuoteNode(level)), $(QuoteNode(fname)), $(QuoteNode(n)), $n)))
        elseif n in argnames
            push!(checks, :($libself($(QuoteNode(level)), $(QuoteNode(fname)), $(QuoteNode(n)), $(GlobalRef(Core, :keep))($n))))
        elseif n === :result
            continue
        else
            error("@enforce_concrete_only: $n is neither a `where` variable, an argument of $fname, nor `result`")
        end
    end
    body = def.args[2]
    if :result in names && !(:result in wherevars) && !(:result in argnames)
        # the body as a function of its own: its inferred result is the method's at this signature
        inner = gensym(:body)
        rt = GlobalRef(Base, :_return_type)
        libres = GlobalRef(@__MODULE__, :_concrete_result)
        body = Expr(:block,
            :(local $inner = () -> $body),
            :($libres($(QuoteNode(level)), $(QuoteNode(fname)), $rt($inner, Tuple{}))),
            :($inner()))
    end
    def.args[2] = Expr(:block, checks..., body)
    return def
end

"""
    VerifyReport

What `verify_main` found: every target the program can reach (signatures), and the calls a trimmed
binary cannot resolve (run-time sites).
"""
struct VerifyReport
    entry::Any
    targets::Vector{Any}
    entrypoints::Vector{Any}    # the targets that no call in the code names: a build is told these;
                                # a signature, or the method instance a cast runs
    holes::Vector{RuntimeSite}
    complete::Bool              # false where the walk stopped at its bound
end
function Base.show(io::IO, ::MIME"text/plain", r::VerifyReport)
    print(io, "verify_main: ", r.entry, "\n  ", length(r.targets), " targets, ", length(r.entrypoints), " of them entry points, ", length(r.holes), " run-time sites")
    for h in first(r.holes, 12)
        print(io, "\n  ", h.file, ":", h.line, "  ", h.call, "\n      ", first(h.cause))
    end
    r.complete || print(io, "\n  (the walk stopped at its bound, after $(length(r.targets)) signatures: the list is not complete)")
end

"""
    verify_main(main, argtypes; entrypoints = true, bound = 100_000) -> VerifyReport

Every target a program reaches from `main` at `argtypes`, for `juliac --trim` (traits §16): the calls
its code resolves, a function passed at a `Callable` at its signature, every declared member as a
target of an operation on a value known by its trait; and the calls left to run time. With
`entrypoints = true`, the targets are signatures a build can compile. The report's `entrypoints` are
the targets that no call in the code names (the members', the casts' and the `Callable`s'): the
signatures to give the build as entry points, and for a cast's member the method instance the cast
runs; `add_entrypoints(report)` gives them to a build. The walk stops after `bound` signatures; the report's
`complete` is then false.
"""
function verify_main(@nospecialize(main), @nospecialize(argtypes::Tuple); entrypoints::Bool = true,
                     bound::Int = _VERIFY_BOUND, world::UInt = Base.get_world_counter())
    sig = Base.signature_type(main, argtypes)
    w = _walk(sig, world; bound)
    # an instance compiled at a set (a `Dynamic` argument) is a target too
    targets = entrypoints ? Any[T for T in w.seen if T isa DataType && !Base.has_free_typevars(T)] : Any[w.seen...]
    return VerifyReport(sig, targets, Any[T for T in w.extra if T isa Core.MethodInstance || T in w.seen], w.sites, w.complete)
end

"""
    add_entrypoints(report::VerifyReport)

Give a `juliac --trim` build the report's entry points (traits §16). Outside a build it does nothing.
"""
function add_entrypoints(r::VerifyReport)
    ccall(:jl_generating_output, Cint, ()) != 0 || return nothing
    for T in r.entrypoints
        if T isa Core.MethodInstance
            T in Base.Compiler._entrypoint_mis || push!(Base.Compiler._entrypoint_mis, T)
        else
            Base.Experimental.entrypoint(T)
        end
    end
    return nothing
end
