# Dynamic{X}: the box, a member of X held so that code for it is compiled once (traits §7.7; lowering §7). The
# struct is Julia's `Core.Dynamic` (compiler §6.9); the library declares its
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
# (lowering §7). Other names are not the trait's: `unwrap` reaches the object itself. The declared
# type is a constant of `X` (`_field_type_at`): inlined at a constant name (`d.u`) the test folds, so a
# read costs the held object's own read and its assertion; at a name not constant it is a scan of `X`'s
# constant table of declared fields.
@inline function Base.getproperty(d::Dynamic{X}, s::Symbol) where {X}
    T = _field_type_at(X, s)
    T === nothing && _not_declared(d, s)
    return getproperty(getfield(d, :object), s)::T
end
@inline function Base.setproperty!(d::Dynamic{X}, s::Symbol, v) where {X}
    T = _field_type_at(X, s)
    T === nothing && _not_declared(d, s)
    _const_at(X, s) && _declared_const(d, s)
    return setproperty!(getfield(d, :object), s, convert(T, v))
end
# the refusals, at the box (the definition-time check reads a call at a box that only throws, traits §7.3)
@noinline _not_declared(d::Dynamic{X}, s::Symbol) where {X} =
    throw(ArgumentError(_runtime_site(string, s, " is not a declared field of ", X, "; unwrap(d) is the object")::String))
@noinline _declared_const(d::Dynamic{X}, s::Symbol) where {X} =
    throw(ArgumentError(_runtime_site(string, s, " is declared @const by ", X)::String))
Base.propertynames(d::Dynamic{X}) where {X} = Tuple(_declared_field_names(X))

# The declared type of the field `s` at the trait instance `X`, or `nothing`: what inference reads
# (compiler §7.1), from the declared fields the library writes on the trait's `TypeName` at its
# declaration (`jl_set_declared_fields`) and its supertraits'. Fixed once `X` is declared, hence
# foldable.
Base.@assume_effects :foldable _dynamic_field_type(@nospecialize(X), s::Symbol) =
    Base.Compiler.declared_field_type(X, s)
# a declared field's name at the instance: a field named by an input is named by its value (`HasProperty{:ps, R}`)
_field_name(c::Contract, f::FieldDecl, env) = f.name in c.inputs ? get(env, f.name, nothing) : f.name

function _field_isconst(@nospecialize(X), s::Symbol)
    for (c, env) in _contracts_of(X), f in c.fields
        _field_name(c, f, env) === s && return f.isconst
    end
    return false
end

function _declared_field_names(@nospecialize(X))
    names = Symbol[]
    for (c, env) in _contracts_of(X), f in c.fields
        n = _field_name(c, f, env)
        n isa Symbol && !(n in names) && push!(names, n)
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
        for i in 1:length(c.params)     # by index (W-170)
            env[c.params[i]] = dt.parameters[i]
        end
    end
    # a trait at other values of its inputs is a trait of its own (traits §3.2)
    for q in out                        # loops here, not Base's `any` and `all` with closures (W-167)
        q[1] === c || continue
        same = true
        for p in c.inputs
            get(q[2], p, nothing) == get(env, p, nothing) || (same = false; break)
        end
        same && return out
    end
    push!(out, (c, env))
    if length(env) == length(c.params)
        for s in c.supers
            _contracts_of!(out, _eval_in(c, s, env, nothing))
        end
    end
    return out
end

# The declared fields at the trait instance `X` as a constant of the type, (names, types, @const flags): fixed once
# `X` is declared, as each field's declared type is (compiler §7.1), so the generator's answer stands. Read as the
# Compiler reads a declared field (`declared_field_type`: the TypeName's declared fields, its supertraits' instances,
# its supertypes'), with no evaluation of a contract's expressions, which a generator may not do.
@generated function _declared_fields(::Type{X}) where {X}
    names, types, consts = Symbol[], Any[], Bool[]
    u = Base.unwrap_unionall(X)
    comps = u isa DataType && u.name === Base.unwrap_unionall(Core.All).name ? (u.parameters[1]::DataType).parameters : Any[u]
    for c in comps
        _fields_in!(names, types, consts, Base.unwrap_unionall(c), 0)
    end
    types = Any[Base.has_free_typevars(T) ? Base.rewrap_unionall(T, X) : T for T in types]
    return QuoteNode((Tuple(names), Tuple(types), Tuple(consts)))
end
_instantiate(@nospecialize(T), tn::Core.TypeName, c::DataType) =
    ccall(:jl_instantiate_type_in_env, Any, (Any, Any, Ptr{Any}), T, tn.wrapper, c.parameters)
function _fields_in!(names::Vector{Symbol}, types::Vector{Any}, consts::Vector{Bool}, @nospecialize(c), depth::Int)
    while c isa DataType && c !== Any
        tn = c.name
        if isdefined(tn, :declared_fields)
            df = tn.declared_fields::Core.SimpleVector
            ks, ts, ct = df[1]::Core.SimpleVector, df[2]::Core.SimpleVector, contract(c)
            for k in 1:length(ks)
                key = ks[k]
                n = key isa TypeVar ? _instantiate(key, tn, c) : key
                (n isa Symbol && !(n in names)) || continue
                T = Base.has_free_typevars(ts[k]) ? _instantiate(ts[k], tn, c) : ts[k]
                f = ct === nothing ? nothing : findfirst(f -> f.name === (key isa TypeVar ? key.name : key), ct.fields)
                push!(names, n); push!(types, T); push!(consts, f !== nothing && ct.fields[f].isconst)
            end
        end
        if depth < 8 && ccall(:jl_is_open_set, Cint, (Any,), c) != 0
            for s in ccall(:jl_supertrait_instances, Any, (Any,), c)::Vector{Any}
                _fields_in!(names, types, consts, Base.unwrap_unionall(s), depth + 1)
            end
        end
        c = c.super
    end
    return nothing
end
# the declared type of the field `s` at `X`, or `nothing`; whether it is `@const`: a scan of the constant table, one
# name at a time, so that at a constant name it folds
@inline _field_type_at(::Type{X}, s::Symbol) where {X} = _scan_fields(s, _declared_fields(X)[1], _declared_fields(X)[2])
@inline _const_at(::Type{X}, s::Symbol) where {X} = _scan_fields(s, _declared_fields(X)[1], _declared_fields(X)[3]) === true
@inline _scan_fields(s::Symbol, ::Tuple{}, ::Tuple{}) = nothing
@inline _scan_fields(s::Symbol, names::Tuple, vals::Tuple) =
    s === names[1] ? vals[1] : _scan_fields(s, Base.tail(names), Base.tail(vals))
