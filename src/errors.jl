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

"A use outside the contract where the contract is required (traits §7.3, §11.3)."
struct TraitUseError <: Exception
    msg::String
end
Base.showerror(io::IO, e::TraitUseError) = print(io, "TraitUseError: ", e.msg)
