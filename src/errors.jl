# The library's errors (traits §11.3). `MethodError` and `TypeError` are Julia's.

"A membership that fails its check: each problem names what is missing or disagrees."
struct ImplementError <: Exception
    trait::Any
    type::Any
    problems::Vector{String}
    method::Bool                  # a method refused at its definition for a member's check (traits §5.10, §5.11)
end
ImplementError(@nospecialize(X), @nospecialize(T), p::AbstractVector) = ImplementError(X, T, convert(Vector{String}, p), false)
ImplementError(@nospecialize(X), @nospecialize(T), p::String) = ImplementError(X, T, [p], false)
"""
A signature as a call, `f(::A, ::B)`, for a message (traits §11.3): never the tuple type
`Tuple{typeof(f), A, B}`, which is the compiler's form.
"""
function _callform(@nospecialize(sig))
    u = Base.unwrap_unionall(sig)
    (u isa DataType && u <: Tuple && !isempty(u.parameters)) || return sprint(show, sig; context = :compact => true)
    ft = u.parameters[1]
    fname = ft isa DataType && isdefined(ft, :instance) ? string(nameof(ft.instance)) :
            ft isa DataType && ft.name === Type.body.name ? sprint(show, ft.parameters[1]; context = :compact => true) :
            string("(::", sprint(show, ft; context = :compact => true), ")")
    args = join(("::" * sprint(show, p; context = :compact => true) for p in u.parameters[2:end]), ", ")
    vars = String[]
    while sig isa UnionAll
        push!(vars, sprint(show, sig.var))
        sig = sig.body
    end
    return string(fname, "(", args, ")", isempty(vars) ? "" : " where {" * join(vars, ", ") * "}")
end

"The error for a method refused at its definition: `T` stays a member of `X`."
_method_refused(@nospecialize(X), @nospecialize(T), p::String) = ImplementError(X, T, [p], true)

function Base.showerror(io::IO, e::ImplementError)
    print(io, "ImplementError: ")
    if e.method
        print(io, "a method is refused: ")
        show(io, e.type)
        print(io, " is a member of ")
        show(io, e.trait)
        print(io, ", and the method would break its check")
    else
        show(io, e.type)
        print(io, " cannot be a member of ")
        show(io, e.trait)
    end
    for p in e.problems
        print(io, "\n  - ", p)
    end
end

"""
    OperationError

A call of a trait's operation that no method of the member takes (traits §11.3): the member's own
methods of the operation are for other arguments. The message names the call, the operation's declared
signature and the member's methods.
"""
struct OperationError <: Exception
    f::Any
    args::Tuple
    trait::Any
end
function Base.showerror(io::IO, e::OperationError)
    f = e.f
    argtypes = map(Core.Typeof, e.args)
    print(io, "OperationError: no method of `", nameof(f), "` takes (", join(("::" * _short_type(T) for T in argtypes), ", "), ")")
    X = bare(e.trait)
    c = try contract(X) catch; nothing end
    if c !== nothing
        for op in c.operations
            op.f === f || continue
            print(io, "\n  `", op.name, "` is declared `", _declared(op, c), "` by ", _short_type(X))
        end
    end
    # the methods of the operation for the member: those that take a member's value where the call has one
    k = findfirst(T -> T <: X, argtypes)
    if k !== nothing
        S = argtypes[k]
        own = String[]
        for m in methods(f)
            _is_trait_method(m) && continue
            sig = Base.unwrap_unionall(m.sig)
            (sig isa DataType && length(sig.parameters) > k) || continue
            p = sig.parameters[k + 1]
            Base.isvarargtype(p) && continue
            p = p isa TypeVar ? p.ub : p
            (p isa Type && S <: p && p !== Any) || continue
            push!(own, _callform(m.sig))
        end
        isempty(own) ? print(io, "\n  ", _short_type(S), " has no method of `", nameof(f), "`") :
                       print(io, "\n  ", _short_type(S), "'s methods of `", nameof(f), "`: ", join(own, ", "))
    end
end
_short_type(@nospecialize(T)) = sprint(show, T; context = :compact => true)

"A use outside the contract where the contract is required (traits §7.3, §11.3)."
struct TraitUseError <: Exception
    msg::String
end
Base.showerror(io::IO, e::TraitUseError) = print(io, "TraitUseError: ", e.msg)
