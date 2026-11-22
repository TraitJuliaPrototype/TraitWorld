# Callable{A, S} (traits §9; lowering §9; compiler §7.4): Julia's `Core.Callable`, a contract at the box. Every
# function is a member of every instance (Base declares `Function`'s entry); a callable type that is no `Function`
# joins by `@implement Callable T`. The library declares the kept forms' memberships, checks the signature where a
# function is boxed or a wrapper enters, and defines `Dynamic{Callable{A, S}}`'s call, which asserts the arguments
# to `A` and the result to `S`.

"""
    Callable{A, S}

The trait of functions called with arguments of the tuple type `A` and returning an `S`. Every function is a
member of every `Callable{A, S}`; the signature is checked where the function is boxed or enters (a method at
`A`, else the `MethodError` a call at `A` would raise), the result asserted to `S` on every call of the box.
Neither `A` nor `S` selects a method. It erases by default. A callable type that is no `Function` joins by
`@implement Callable T`.
"""
const Callable = Core.Callable

# Dynamic{Z} for Z <: Callable{A, S} is a member of Callable{A, S}, forwarding to its object
let A = TypeVar(:A, Tuple), S = TypeVar(:S), Z = TypeVar(:Z, Core.Callable{A, S})
    pattern = UnionAll(A, UnionAll(S, UnionAll(Z, Dynamic{Z})))
    _declare!(pattern, Core.Callable{A, S}, @__MODULE__, :object, :field)
end
# and the wrapper's (W-151): Compiled{Z} where {A, S, Z <: Callable{A, S}}
let A = TypeVar(:A, Tuple), S = TypeVar(:S), Z = TypeVar(:Z, Core.Callable{A, S})
    pattern = UnionAll(A, UnionAll(S, UnionAll(Z, Compiled{Z})))
    _declare!(pattern, Core.Callable{A, S}, @__MODULE__, :object, :field)
end

# Dynamic{Callable{A, S}}'s call: the arguments at A, the result checked against S. At the box of one signature
# `A` and `S` are the box's own parameters, known where the call is compiled, and the result is checked in the
# method's body: in code compiled by facts a call of a helper with the result, whose type is not known, is a
# run-time site (E-442: Julia's dynamic call, against 166 ns a call).
function (d::Dynamic{Core.Callable{A, S}})(args...) where {A, S}
    args isa A || throw(MethodError(getfield(d, :object), args))
    r = getfield(d, :object)(args...)
    r isa S || throw(TypeError(:Callable, S === Nothing ? "end the function with `nothing`" : "", S, r))
    return r::S
end
# Boxed at several signatures (`Dynamic{All{Callable{A, S}, Callable{B, S}}}`, traits §7.7), the call takes the one
# its arguments match. The result is checked in the body, as at one signature: a helper called with the result, whose
# type is not known, is a run-time site in code compiled by facts.
function (d::Dynamic{Z})(args...) where {A, S, Z <: Core.Callable{A, S}}
    sigs = _signatures(Z)
    sigs === () || return _call_at_signatures(d, args, sigs)
    args isa A || throw(MethodError(getfield(d, :object), args))     # a trait below `Callable{A, S}`: its bound's
    r = getfield(d, :object)(args...)
    r isa S || throw(TypeError(:Callable, S === Nothing ? "end the function with `nothing`" : "", S, r))
    return r::S
end
# the signatures taken one by one, each `A2` and `S2` a constant where the call is compiled: a loop over the tuple
# would give them as a union, and a closed build could resolve neither the test nor the result (compiler §7.6)
@inline _call_at_signatures(d::Dynamic, args::Tuple, ::Tuple{}) = throw(MethodError(getfield(d, :object), args))
@inline function _call_at_signatures(d::Dynamic, args::Tuple, sigs::Tuple)
    A2, S2 = sigs[1]
    args isa A2 || return _call_at_signatures(d, args, Base.tail(sigs))
    r = getfield(d, :object)(args...)
    r isa S2 || throw(TypeError(:Callable, S2 === Nothing ? "end the function with `nothing`" : "", S2, r))
    return r::S2
end
# the signatures of an intersection of `Callable`s, as (A, S) pairs: a constant of the type, so a call of a
# `Dynamic{All{Callable…}}` at its second signature builds nothing (E-307)
# `_signatures_of` stands before the generated function that calls it: a generator runs in the world of its
# definition, so loaded from source it does not see a function defined after it.
function _signatures_of(@nospecialize(u))
    u isa DataType || return ()
    if u.name === Base.unwrap_unionall(Core.All).name
        return Tuple(Iterators.flatten(_signatures_of(c) for c in (u.parameters[1]::DataType).parameters))
    end
    u.name === Base.unwrap_unionall(Core.Callable).name && length(u.parameters) >= 2 && return ((u.parameters[1], u.parameters[2]),)
    return ()
end
@generated _signatures(::Type{Z}) where {Z} = _signatures_of(Base.unwrap_unionall(Z))

# The signature check (traits §9): `f` has a method at each `Callable` signature of the trait `Z` (a `Callable`, or
# an intersection with such components). A fact where `f`'s type is known: `hasmethod` at a declared signature folds,
# with its edge to `f`'s dispatch there.
@inline _callable_met(::Type{Z}, @nospecialize(f)) where {Z} = _first_unmet(f, _signatures(Z)) === nothing
# the first signature `A` at which `f` has no method, or `nothing`: one by one, so that each test is at a constant `A`
@inline _first_unmet(@nospecialize(f), ::Tuple{}) = nothing
@inline _first_unmet(@nospecialize(f), sigs::Tuple) =
    hasmethod(f, sigs[1][1]) ? _first_unmet(f, Base.tail(sigs)) : sigs[1][1]
# where the function is boxed by a forwarder: the MethodError of the call that passes it (the method's own call)
@inline _callable_box_check(::Type{Dynamic{Z}}, @nospecialize(f), @nospecialize(self), args::Tuple) where {Z} =
    (_callable_met(Z, f) || throw(MethodError(self, args)); nothing)
# where a wrapper enters a method at `Callable{A, S}`: the same test, and (GT-24 (b), mine) a function whose result
# inferred at `A` is outside `S` is refused there too, by the TypeError a call's result would raise
@inline function _callable_entry_check(::Type{Z}, @nospecialize(f), @nospecialize(self), args::Tuple) where {Z}
    _callable_met(Z, f) || throw(MethodError(self, args))
    for (A, S) in _signatures(Z)
        rt = Core.Compiler.return_type(Tuple{Core.Typeof(f), (A::DataType).parameters...})
        (rt === Union{} || typeintersect(rt, S) !== Union{}) ||
            throw(TypeError(:Callable, "the result of the function at $(A) infers as $(rt)", S, f))
    end
    return nothing
end

# `Dynamic{Callable{A, S}}(f)` written out: the signature checked, the MethodError of a call at `A` (traits §9)
function (::Type{D})(f::Function) where {Z <: Core.Callable, D <: Dynamic{Z}}
    D isa DataType || throw(ArgumentError("Dynamic{X} needs the trait's parameters"))
    A = _first_unmet(f, _signatures(Z))
    A === nothing || throw(MethodError(f, A))
    return _new_box(D, f)
end

# A callable type that is no `Function` joins `Callable` (traits §9; lowering §9): one entry whose instance,
# `Callable` itself, leaves both inputs free, by the type's owner.
function _implement_callable!(mod::Module, @nospecialize(member))
    member isa Type && member <: Function &&
        throw(ArgumentError("$member is a Function: a member of every Callable already"))
    _check_membership_owner(mod, Core.Callable, member)
    _declare_checked!(member, Core.Callable, mod, nothing, :self)
    return nothing
end
