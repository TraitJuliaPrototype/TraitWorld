# The library's errors (traits §11.3). `MethodError` and `TypeError` are Julia's.

"A membership that fails its check: each problem names what is missing or disagrees."
struct ImplementError <: Exception
    trait::Any
    type::Any
    problems::Vector{String}
end
ImplementError(@nospecialize(X), @nospecialize(T), p::String) = ImplementError(X, T, [p])

function Base.showerror(io::IO, e::ImplementError)
    print(io, "ImplementError: ")
    show(io, e.type)
    print(io, " cannot be a member of ")
    show(io, e.trait)
    for p in e.problems
        print(io, "\n  - ", p)
    end
end

"A use outside the contract where the contract is required (traits §7.3, §11.3)."
struct TraitUseError <: Exception
    msg::String
end
Base.showerror(io::IO, e::TraitUseError) = print(io, "TraitUseError: ", e.msg)
