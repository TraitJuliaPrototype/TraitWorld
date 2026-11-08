# Dynamic{X}: a member of X kept with the attribute `Dynamic` (traits §7.7; lowering §7). The struct
# is Julia's `Core.Dynamic`, so that the compiler can make one for `keep`; the library declares its
# memberships (each trait's, at `@trait`) and defines its methods here.

"""
    Dynamic{X}(x)

A member `x` of the trait `X`, held so that code for it is compiled once: its operations
dispatch on the held object when they run, with their declared results. `X` is a trait with its
parameters. `Dynamic{X}` is a member of `X` and of `X`'s supertraits only.
"""
const Dynamic = Core.Dynamic

"""
    unwrap(d::Dynamic)

The object `d` holds.
"""
unwrap(d::Dynamic) = getfield(d, :object)

# equality by the objects' identity (traits §8.3)
Base.:(==)(a::Dynamic, b::Dynamic) = getfield(a, :object) === getfield(b, :object)
Base.isequal(a::Dynamic, b::Dynamic) = getfield(a, :object) === getfield(b, :object)
Base.hash(d::Dynamic, h::UInt) = hash(objectid(getfield(d, :object)), hash(:Dynamic, h))

function Base.show(io::IO, d::Dynamic{X}) where {X}
    print(io, "Dynamic{")
    show(io, X)
    print(io, "}(")
    show(io, getfield(d, :object))
    print(io, ")")
end

# Every trait Dynamic{X} is a member of forwards to its object (lowering §2, §7).
_fwd(d::Dynamic, @nospecialize(X::Type)) = getfield(d, :object)

# The declared fields are read and written on the held object, asserted to the declared type
# (lowering §7). Other names are not the trait's: `unwrap` reaches the object itself.
function Base.getproperty(d::Dynamic{X}, s::Symbol) where {X}
    T = _dynamic_field_type(X, s)
    T === nothing && throw(ArgumentError("$s is not a declared field of $X; unwrap(d) is the object"))
    return getproperty(getfield(d, :object), s)::T
end
function Base.setproperty!(d::Dynamic{X}, s::Symbol, v) where {X}
    T = _dynamic_field_type(X, s)
    T === nothing && throw(ArgumentError("$s is not a declared field of $X; unwrap(d) is the object"))
    _field_isconst(X, s) && throw(ArgumentError("$s is declared @const by $X"))
    return setproperty!(getfield(d, :object), s, convert(T, v))
end
Base.propertynames(d::Dynamic{X}) where {X} = Tuple(_declared_field_names(X))

const _DYNAMIC_FIELDS = IdDict{Any,Any}()   # (X, name) => the declared type, or nothing

function _dynamic_field_type(@nospecialize(X), s::Symbol)
    key = (X, s)
    return get!(_DYNAMIC_FIELDS, key) do
        for (c, env) in _contracts_of(X)
            for f in c.fields
                f.name === s && return _eval_in(c, f.type, env, nothing)
            end
        end
        return nothing
    end
end

function _field_isconst(@nospecialize(X), s::Symbol)
    for (c, _) in _contracts_of(X), f in c.fields
        f.name === s && return f.isconst
    end
    return false
end

function _declared_field_names(@nospecialize(X))
    names = Symbol[]
    for (c, _) in _contracts_of(X), f in c.fields
        f.name in names || push!(names, f.name)
    end
    return names
end

# The contracts that apply at the trait instance X: its own and its supertraits', each with
# its parameters' values (from X's parameters, through the supertraits' instances).
function _contracts_of(@nospecialize(X))
    out = Tuple{Contract,Dict{Symbol,Any}}[]
    _contracts_of!(out, X)
    return out
end
function _contracts_of!(out, @nospecialize(X))
    c = contract(X)
    c === nothing && return out
    env = Dict{Symbol,Any}()
    dt = Base.unwrap_unionall(X)::DataType
    if X isa DataType
        for (i, p) in enumerate(c.params)
            env[p] = dt.parameters[i]
        end
    end
    # a trait at other values of its inputs is a trait of its own (traits §3.2)
    any(q -> q[1] === c && all(p -> get(q[2], p, nothing) == get(env, p, nothing), c.inputs), out) && return out
    push!(out, (c, env))
    if length(env) == length(c.params)
        for s in c.supers
            _contracts_of!(out, _eval_in(c, s, env, nothing))
        end
    end
    return out
end
