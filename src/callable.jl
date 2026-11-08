# Callable{A, S} (traits §9; lowering §9; compiler §7.4): Julia's `Core.Callable`, a set whose
# memberships the functions' own methods decide. The library declares one membership for it,
# `Dynamic{Z}`'s, and `Dynamic{Callable{A, S}}`'s call, which asserts the arguments to `A` and the
# result to `S`.

"""
    Callable{A, S}

The trait of functions called with arguments of the tuple type `A` and returning an `S`: a function is
a member where it has a method for a call at `A`, whatever `S` is. Dispatch picks by the arguments'
signature; a call through a value known as a `Callable{A, S}` has the result type `S`, checked on
return. Its default attribute is `Dynamic`.
"""
const Callable = Core.Callable

# Dynamic{Z} for Z <: Callable{A, S} is a member of Callable{A, S}, forwarding to its object
let A = TypeVar(:A, Tuple), S = TypeVar(:S), Z = TypeVar(:Z, Core.Callable{A, S})
    pattern = UnionAll(A, UnionAll(S, UnionAll(Z, Dynamic{Z})))
    _declare!(pattern, Core.Callable{A, S}, @__MODULE__, :object, :field)
end

# Dynamic{Callable{A, S}}'s call: the arguments at A, the result checked against S. Kept at several signatures
# (`Dynamic{All{Callable{A, S}, Callable{B, S}}}`, traits §7.7), the call takes the one its arguments match.
function (d::Dynamic{Z})(args...) where {A, S, Z <: Core.Callable{A, S}}
    args isa A && return _checked_result(getfield(d, :object)(args...), S)
    for (A2, S2) in _signatures(Z)
        args isa A2 && return _checked_result(getfield(d, :object)(args...), S2)
    end
    throw(MethodError(getfield(d, :object), args))
end
@inline function _checked_result(r, ::Type{S}) where {S}
    r isa S || throw(TypeError(:Callable, S === Nothing ? "end the function with `nothing`" : "", S, r))
    return r::S
end
# the signatures of an intersection of `Callable`s, as (A, S) pairs
_signatures(@nospecialize(Z)) = _signatures_of(Base.unwrap_unionall(Z))
function _signatures_of(@nospecialize(u))
    u isa DataType || return ()
    if u.name === Base.unwrap_unionall(Core.All).name
        return Tuple(Iterators.flatten(_signatures_of(c) for c in (u.parameters[1]::DataType).parameters))
    end
    u.name === Base.unwrap_unionall(Core.Callable).name && length(u.parameters) >= 2 && return ((u.parameters[1], u.parameters[2]),)
    return ()
end
