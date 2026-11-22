# The runtime's interface for sets and memberships (compiler §4).

"""
    _runtime_site(f, args...)

`f(args...)` as a run-time site (facts §5): `f` is passed typed `Any`, so the caller records no edge to the code it
reaches, and that code is compiled where it first runs. The library's code is compiled by facts, and each hook must be
in the deep class (compiler §3.2), so that no unrelated load ends it (G2). Its calls into code outside the class go
through here: the code that handles values of any type by its purpose (a message that prints a user's type or method,
the logger the user installed) and Base's code over values its types do not settle. The result is typed `Any`.

Written as a call in the latest world: in a session inference follows no such call, and the hooks run in the latest
world as it is (compiler §10.1); in a closed build a call in the latest world is the call (compiler §7.6), so the
build resolves it. A call at a function typed `Any` would be a call no closed build can resolve.
"""
_runtime_site(f, args...) = Base.invokelatest(f, args...)

# Helpers over containers of `Any` that stay in the deep class: a loop in the library's own code, where a call at a
# value typed `Any` is a run-time site; Base's `any`, `findfirst`, `enumerate` and the like over such a container
# are plain code that commits at `Any` (open issue 218). A store of a value of a known type into a `Dict{Symbol,Any}`
# reaches Base's method that takes any value (`@nospecialize`), outside the class: `_setenv!` takes the value typed
# `Any`, so that the store is a run-time site.
"whether `x` is in `v`, by `===`"
function _in_by_identity(@nospecialize(x), v::Vector{Any})
    for y in v
        y === x && return true
    end
    return false
end
_setenv!(d::Dict{Symbol,Any}, k::Symbol, @nospecialize(v)) = (d[k] = Base.inferencebarrier(v); d)

_open_set!(@nospecialize(T)) = ccall(:jl_set_open_set, Cvoid, (Any,), T)
_set_contract!(@nospecialize(T), @nospecialize(c)) = ccall(:jl_set_contract, Cvoid, (Any, Any), T, c)
"Mark a set's input parameters (compiler §4.6): bit i for parameter i, the first eight only."
_set_inputs!(@nospecialize(T), mask::UInt8) = ccall(:jl_set_input_params, Cvoid, (Any, UInt8), T, mask)

"Declare `member` a member of `instance` (compiler §4.2). The caller continues with `Expr(:latestworld)`."
function _declare!(@nospecialize(member), @nospecialize(instance), mod::Module,
                   @nospecialize(by), receiver::Symbol)
    return ccall(:jl_declare_membership, Any, (Any, Any, Any, Any, Any),
                 member, instance, mod, by, receiver)
end

"`_declare!` where a refusal (a cycle, another instance, strict mode's ambiguity) is an `ImplementError`."
function _declare_checked!(@nospecialize(member), @nospecialize(instance), mod::Module,
                           @nospecialize(by), receiver::Symbol)
    refusal = try
        return _declare!(member, instance, mod, by, receiver)
    catch err
        err isa ErrorException || rethrow()
        err.msg
    end
    throw(ImplementError(instance, member, refusal))      # outside the catch: the message prints once
end

"whether `X` is a trait: an open set"
istrait(@nospecialize(X)) = (dt = Base.unwrap_unionall(X); dt isa DataType && ccall(:jl_is_open_set, Cint, (Any,), dt) != 0)

# The default's method of an operation: the trait's method of `f` defined last in `mod` at this arity.
function _default_method(@nospecialize(f), mod::Module, nargs::Int)
    best = nothing
    for m in methods(f)
        (m.module === mod && Int(m.nargs) == nargs && _is_trait_method(m)) || continue
        (best === nothing || m.primary_world > best.primary_world) && (best = m)
    end
    return best
end

# A trait's operations for the compiler (compiler §4.1): each entry `(f, sig, rt, default, vars)` with the
# signature and result in the variables `vars`, wrapped in those that occur. Written once, at the declaration.
function _set_operations!(@nospecialize(X), entries::Vector{Any})
    out = Any[]
    for e in entries
        e === nothing && continue
        f, sig, rt, default, vars = e
        (rt isa Type || rt isa TypeVar) || continue
        for v in reverse(vars)
            v isa TypeVar || continue
            any(w -> w === v, _free_vars(sig)) && (sig = UnionAll(v, sig))
        end
        push!(out, Core.svec(f, sig, rt, default))
    end
    ccall(:jl_set_contract_operations, Cvoid, (Any, Any), X, Core.svec(out...))
    return nothing
end

# A trait's declared fields for inference (compiler §7.1): their types evaluated with the variables
# of the trait's wrapper; a type that names `Self` is recorded as `Any`. A field named by an input
# parameter (`HasProperty{N, R}`'s `N`) is recorded under that parameter's variable.
function _set_declared_fields!(@nospecialize(X), mod::Module, names::Vector{Symbol}, tyexs::Vector{Any},
                               inputs::Vector{Symbol} = Symbol[])
    w = Base.unwrap_unionall(X).name.wrapper
    vars = TypeVar[]
    s = w
    while s isa UnionAll
        push!(vars, s.var)
        s = s.body
    end
    types = Any[]
    for ex in tyexs
        T = ex === nothing || _mentions(ex, :Self) ? Any :
            Core.eval(mod, Expr(:let, Expr(:block, Any[:($(v.name) = $v) for v in vars]...), ex))
        push!(types, T isa Type || T isa TypeVar ? T : Any)
    end
    keys = Any[n in inputs ? vars[findfirst(v -> v.name === n, vars)::Int] : n for n in names]
    ccall(:jl_set_declared_fields, Cvoid, (Any, Any, Any), X, Core.svec(keys...), Core.svec(types...))
    return nothing
end
