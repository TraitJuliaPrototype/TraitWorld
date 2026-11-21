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

"""
A method as its signature is written, `colsum(t::ColTable)`, for a message (traits §11.3): a keyword method's body as
its function with the keywords, `f(t::ColTable; k::Float64)`; a closure as `(t::ColTable) -> …`, with the function it
is written in. Never a generated name.
"""
function _written_method(m::Method)
    tv, decls, _, _ = Base.arg_decl_parts(m)
    arg((n, t)) = isempty(n) || startswith(n, "#") ? "::" * t : (t == "Any" || isempty(t)) ? n : n * "::" * t
    name = string(m.name)
    args = decls[2:end]
    kws = Tuple{String,String}[]
    kb = match(r"^#([^#]+)#\d+$", name)
    if kb !== nothing
        # a keyword method's body, `#f#4(k::Float64, ::typeof(f), t::ColTable)`: its keywords, then its function
        f = kb.captures[1]
        j = findfirst(d -> startswith(d[2], "typeof(") && (d[2] == "typeof($f)" || endswith(d[2], ".$f)")), args)
        if j !== nothing
            kws, args, name = args[1:j-1], args[j+1:end], f
        end
    end
    call = string("(", join(map(arg, args), ", "), isempty(kws) ? "" : "; " * join(map(arg, kws), ", "), ")")
    wh = isempty(tv) ? "" : " where " * (length(tv) == 1 ? string(tv[1]) : "{" * join(string.(tv), ", ") * "}")
    if startswith(name, "#")
        # a closure, `#outer##0`, or an anonymous function at top level, `#7`
        cl = match(r"^#([^#]+)##\d+$", name)
        return string("`", call, wh, " -> …`", cl === nothing ? "" : " in `$(cl.captures[1])`")
    end
    return string("`", name, call, wh, "`")
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

_short_type(@nospecialize(T)) = sprint(show, T; context = :compact => true)

"A use outside the contract where the contract is required (traits §7.3, §11.3)."
struct TraitUseError <: Exception
    msg::String
end
Base.showerror(io::IO, e::TraitUseError) = print(io, "TraitUseError: ", e.msg)
