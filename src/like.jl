# like and withfields (traits §6.5; lowering §8).

"""
    like(t, x)

A value like `t`, built from `x`: where `t`'s type serves its trait by its own methods, `x`
itself (of `t`'s type family); where it forwards by a field, `t`'s type rebuilt by its
positional constructor with the forwarding field replaced by `x`; on a `Dynamic{X}`, a
`Dynamic{X}` of `x`.
"""
like(t, x) = t isa Dynamic ? typeof(t)(x) : _like(t, x)

# A member that forwards by a field has a method of `_like` of its own, made at its `@implement … by f`
# (`_define_like!`): the constructor called by position, with nothing to look up when it runs. Any
# other type serves its trait by its own methods.
function _like(t, x)
    S = typeof(t)
    typeof(x).name === S.name ||
        throw(ArgumentError("like(t, x): t's type $S serves its trait by its own methods, so x must be of its family, $(S.name.wrapper); got $(typeof(x))"))
    return x
end

# whether a type has a constructor that could take every field in order
_has_positional(C, n::Int) = any(m -> (s = Base.unwrap_unionall(m.sig); s isa DataType &&
    (length(s.parameters) - 1 == n || (m.isva && length(s.parameters) - 2 <= n))), methods(C))

# the hint on the constructor's method error (hints.jl): a struct called with as many arguments as it has
# fields, and no constructor that takes them
function _positional_hint!(lines, @nospecialize(f), args)
    (f isa Type && (S = Base.unwrap_unionall(f)) isa DataType && isstructtype(S)) || return
    (fieldcount(S) == length(args) && !_has_positional(f, fieldcount(S))) || return
    push!(lines, "`like` and `withfields` rebuild a $(nameof(S.name.wrapper)) by its positional constructor, with every field in order; " *
        "$(nameof(S.name.wrapper)) has none that takes its $(fieldcount(S)) fields " *
        "($(join(("::" * _tstr(T) for T in fieldtypes(S)), ", "))). Define one (an inner constructor has replaced the default).")
    return
end

# `_like` for a member that forwards by the field `by` (lowering §8), defined in the declaring module
# as the member's forwarding methods are. The first forwarding field declared for a type is the one
# rebuilt. Returns the method made, or nothing.
function _define_like!(mod::Module, @nospecialize(member), by::Symbol)
    S = Base.unwrap_unionall(member)
    (S isa DataType && isstructtype(S) && hasfield(S, by)) || return nothing
    for m in methods(_like)
        Base.unwrap_unionall(m.sig).parameters[2] == S && return nothing     # declared before, by a field
    end
    C = S.name.wrapper
    lk = GlobalRef(@__MODULE__, :_like)
    k = Base.fieldindex(S, by)
    body = Expr(:call, C, (i == k ? :x : :(getfield(t, $i)) for i in 1:fieldcount(S))...)
    Core.eval(mod, :($lk(t::$member, x) = $body))
    return which(_like, Tuple{S, Any})
end

"""
    withfields(t; name = v, …)

`t` rebuilt by its type's positional constructor, with the named fields replaced. On a `Dynamic{X}`, the object
it holds rebuilt and boxed at `X` (a declared field of `X` only; a rebuilt object that is no member of `X` is
refused by the box); on a wrapper, the wrapper of the rebuilt object.
"""
withfields(t; kw...) = _withfields(t, values(kw))

_withfields(t, nt::NamedTuple) = _rebuilt(t, nt)
# a box (traits §6.5): its object rebuilt, boxed as any box is. Behind the box only the contract reaches the
# object, so a name is one of `X`'s declared fields, as the box's `getproperty` asks; the test folds at a
# constant name. The inner call is at a value known only by its trait (lowering §8).
function _withfields(d::Dynamic{X}, nt::NamedTuple{names}) where {X, names}
    s = _first_undeclared(X, names)
    s === nothing || throw(ArgumentError("withfields: $s is not a declared field of $X; withfields(unwrap(d); …) rebuilds the object"))
    # every constructor of the box gives a `Dynamic{X}`; at an argument of unknown type inference joins them as `Any`
    return Dynamic{X}(_rebuilt(getfield(d, :object), nt))::Dynamic{X}
end
# a wrapper: the wrapper of its object rebuilt
_withfields(w::Compiled, nt::NamedTuple) = Compiled(_rebuilt(getfield(w, :object), nt))

Base.@assume_effects :foldable function _first_undeclared(@nospecialize(X), names::Tuple)
    for s in names
        _dynamic_field_type(X, s) === nothing && return s
    end
    return nothing
end

# the constructor's call by position, made from the type and the names: nothing is looked up when it runs
@generated function _rebuilt(t::T, nt::NamedTuple{names}) where {T, names}
    for k in names
        hasfield(T, k) || return :(throw(ArgumentError(string("withfields: ", $T, " has no field ", $(QuoteNode(k))))))
    end
    C = T.name.wrapper
    args = Any[n in names ? :(getfield(nt, $(QuoteNode(n)))) : :(getfield(t, $(QuoteNode(n)))) for n in fieldnames(T)]
    return Expr(:call, C, args...)
end
