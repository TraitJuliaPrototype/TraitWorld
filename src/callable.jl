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

# Dynamic{Callable{A, S}}'s call: the arguments at A, the result checked against S
function (d::Dynamic{Z})(args...) where {A, S, Z <: Core.Callable{A, S}}
    args isa A || throw(MethodError(getfield(d, :object), args))
    r = getfield(d, :object)(args...)
    r isa S || throw(TypeError(:Callable, S === Nothing ? "end the function with `nothing`" : "", S, r))
    return r::S
end
