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
