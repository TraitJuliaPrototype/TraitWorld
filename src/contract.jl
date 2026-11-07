# A trait's contract (traits §4; lowering §2), kept on the trait's TypeName (compiler §4.1).
# Type expressions are kept as written and evaluated in the declaring module, with the trait's
# parameters and `Self` bound to the values of the member being checked.

"An operation: a generic function with declared argument types and a declared result (traits §4.1)."
struct OperationDecl
    name::Symbol                  # the function's name, as written (`length` for `Base.length`)
    f::Any                        # the generic function
    args::Vector{Pair{Symbol,Any}}  # argument names => declared type expressions
    vararg::Bool                  # whether the last argument is a vararg
    receiver::Int                 # the receiver's position
    result::Any                   # the declared result's expression
    wherevars::Vector{Any}        # the operation's own `where` variables, as written
    hasdefault::Bool              # whether the trait gives a default (traits §4.2)
end

"A declared field (traits §4.3)."
struct FieldDecl
    name::Symbol
    type::Any                     # expression
    isconst::Bool                 # `@const`: read-only through the trait
end

"A trait's contract: what each membership is checked against (traits §5.10)."
struct Contract
    trait::Any                    # the trait, bare
    mod::Module                   # the declaring module
    params::Vector{Symbol}
    bounds::Vector{Any}           # each parameter's bound's expression, `nothing` if none
    inputs::Vector{Symbol}        # `@input` parameters
    supers::Vector{Any}           # the supertraits' instances, as expressions of the parameters
    operations::Vector{OperationDecl}
    fields::Vector{FieldDecl}
    equations::Vector{Pair{Symbol,Any}}  # a parameter => an expression of `Self`
    attribute::Symbol             # :none, :dynamic or :compiled (traits §4.6; W-111)
    concrete::Vector{Pair{Symbol,Symbol}}  # a parameter or :Self => :enforce or :warn (traits §14)
end

"""
    contract(X) -> Contract or nothing

The contract of the trait `X`, from its TypeName's contract slot.
"""
function contract(@nospecialize(X))
    dt = Base.unwrap_unionall(X)
    dt isa DataType || return nothing
    tn = dt.name
    isdefined(tn, :contract) || return nothing
    c = getfield(tn, :contract)
    return c isa Contract ? c : nothing
end

"the trait's bare type: `X` for `X{Int}`"
bare(@nospecialize(X)) = (Base.unwrap_unionall(X)::DataType).name.wrapper

# Evaluate a type expression of the contract with the parameters' values and `Self` bound. The
# forms contracts use (names, `X{…}`, calls such as `eltype(Self)`, `M.name`) are evaluated without
# `eval`: a membership checked while another package's image is built may not evaluate into the
# trait's module. Any other form falls back to `eval` there.
function _eval_in(c::Contract, @nospecialize(ex), env::AbstractDict{Symbol}, @nospecialize(self))
    v = _eval_pure(c.mod, ex, env, self)
    v isa _NotPure || return v
    binds = Any[Expr(:(=), p, QuoteNode(v)) for (p, v) in env]
    self === nothing || push!(binds, Expr(:(=), :Self, QuoteNode(self)))
    return Core.eval(c.mod, Expr(:let, Expr(:block, binds...), ex))
end

struct _NotPure end

function _eval_pure(mod::Module, @nospecialize(ex), env::AbstractDict{Symbol}, @nospecialize(self))
    if ex isa Symbol
        ex === :Self && self !== nothing && return self
        haskey(env, ex) && return env[ex]
        return isdefined(mod, ex) ? getglobal(mod, ex) : _NotPure()
    elseif ex isa QuoteNode
        return ex.value
    elseif !(ex isa Expr)
        return ex
    elseif ex.head === :. && length(ex.args) == 2 && ex.args[2] isa QuoteNode
        m = _eval_pure(mod, ex.args[1], env, self)
        m isa _NotPure && return m
        return getproperty(m, ex.args[2].value)
    elseif ex.head === :curly || ex.head === :call
        args = Any[]
        for a in ex.args
            v = _eval_pure(mod, a, env, self)
            v isa _NotPure && return v
            push!(args, v)
        end
        return ex.head === :curly ? Core.apply_type(args...) : args[1](args[2:end]...)
    end
    return _NotPure()
end
