# The runtime's interface for sets and memberships (compiler §4).

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
    try
        return _declare!(member, instance, mod, by, receiver)
    catch err
        err isa ErrorException || rethrow()
        throw(ImplementError(instance, member, err.msg))
    end
end

"whether `X` is a trait: an open set"
istrait(@nospecialize(X)) = (dt = Base.unwrap_unionall(X); dt isa DataType && ccall(:jl_is_open_set, Cint, (Any,), dt) != 0)

# The trait's method for an operation carries the operation's declared result, with the flag that
# it covers every member: each member's serving method is checked to infer within it (compiler
# §6.8; traits §5.10). The method is the trait's method of `f` defined last in `mod` at this arity;
# the result is evaluated with the method's own type variables.
function _set_declared!(@nospecialize(f), mod::Module, nargs::Int, @nospecialize(resultex))
    best = nothing
    for m in methods(f)
        (m.module === mod && Int(m.nargs) == nargs && _is_trait_method(m)) || continue
        (best === nothing || m.primary_world > best.primary_world) && (best = m)
    end
    best === nothing && return nothing
    vars = TypeVar[]
    s = best.sig
    while s isa UnionAll
        push!(vars, s.var)
        s = s.body
    end
    rt = Core.eval(mod, Expr(:let, Expr(:block, Any[:($(v.name) = $v) for v in vars]...), resultex))
    (rt isa Type || rt isa TypeVar) || return nothing
    ccall(:jl_method_set_declared_result, Cvoid, (Any, Any, Cint), best, rt, 1)
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
