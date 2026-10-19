# ---------------------------------------------------------------------------
# The fully-typed certificate (design.md §3.4, decided in session 29): code is fully typed when every
# call on a normal path, in it and in everything it reaches, is at a fact signature. For such code
# the facts rule costs nothing: facts inference is plain inference there. A run-time site (a call at
# abstract argument types, a function value not known) pays the facts rule's cost: its result is
# `Any`, and the code after it is not fully typed either. An operation on a `Dynamic` value is a
# declared run-time site (the heterogeneity is declared, its result type too): it is counted, not
# reported. The walk is verify_main's: what the code runs (code compiled by facts), error paths left
# out.
# ---------------------------------------------------------------------------

"""
    FullyTypedReport

What `fully_typed` found: the run-time sites on normal paths (none for fully typed code), and the
number of declared dynamic sites (operations on `Dynamic` values).
"""
struct FullyTypedReport
    entry::Any
    sites::Vector{Hole}
    dynamic::Int
end

"Whether the code `fully_typed` checked is fully typed: no run-time site on a normal path."
isfullytyped(r::FullyTypedReport) = isempty(r.sites)

"""
    fully_typed(f, argtypes) -> FullyTypedReport

Check that `f` at `argtypes`, and everything it reaches, is fully typed: every call on a normal path
at a fact signature. Fully typed code pays nothing for the facts rule.
"""
function fully_typed(@nospecialize(f), @nospecialize(argtypes::Tuple))
    # walked from a caller at the arguments' types, as a call site sees `f` (an entry is a boundary,
    # compiled in its caller's mode)
    r = verify_main(_certified_call, (Core.Typeof(f), argtypes...))
    sites = Hole[h for h in r.holes if !h.errorpath && h.kind !== :dynamic]
    ndyn = count(p -> p.first === :dynamic, r.targets) + count(h -> h.kind === :dynamic, r.holes)
    return FullyTypedReport(Base.signature_type(f, argtypes), sites, ndyn)
end
"The caller `fully_typed` walks from: a call of `f` at the arguments' types (fixed arities with type parameters, so that a `Type{T}` argument stays `Type{T}`: a varargs signature would widen it to a kind). The call is not inlined: the walk sees `f`'s code as `f`'s, not as this helper's."
_certified_call(f::F) where {F} = @noinline f()
_certified_call(f::F, a1::A1) where {F,A1} = @noinline f(a1)
_certified_call(f::F, a1::A1, a2::A2) where {F,A1,A2} = @noinline f(a1, a2)
_certified_call(f::F, a1::A1, a2::A2, a3::A3) where {F,A1,A2,A3} = @noinline f(a1, a2, a3)
_certified_call(f::F, a1::A1, a2::A2, a3::A3, a4::A4) where {F,A1,A2,A3,A4} = @noinline f(a1, a2, a3, a4)
_certified_call(f::F, a1::A1, a2::A2, a3::A3, a4::A4, a5::A5) where {F,A1,A2,A3,A4,A5} = @noinline f(a1, a2, a3, a4, a5)
_certified_call(f::F, a1::A1, a2::A2, a3::A3, a4::A4, a5::A5, a6::A6) where {F,A1,A2,A3,A4,A5,A6} = @noinline f(a1, a2, a3, a4, a5, a6)
_certified_call(f::F, a1::A1, a2::A2, a3::A3, a4::A4, a5::A5, a6::A6, a7::A7) where {F,A1,A2,A3,A4,A5,A6,A7} = @noinline f(a1, a2, a3, a4, a5, a6, a7)
_certified_call(f::F, a1::A1, a2::A2, a3::A3, a4::A4, a5::A5, a6::A6, a7::A7, a8::A8) where {F,A1,A2,A3,A4,A5,A6,A7,A8} = @noinline f(a1, a2, a3, a4, a5, a6, a7, a8)
_certified_call(f::F, args::Vararg{Any,N}) where {F,N} = @noinline f(args...)

"How to make a run-time site a fact, by its kind."
function _site_hint(h::Hole)
    k = h.kind
    k === :dispatch && return "its arguments are not concrete, so its result is `Any`: give the values concrete types (a typed field or container, a function barrier), or declare them `Dynamic{X}` with a trait that declares the result type"
    k === :callee && return "the function called is not known: pass it as a `Callable{A, S}`, or store it with a concrete type"
    k === :splat && return "a splat of a collection: pass a tuple, or the elements"
    k === :latest && return "a call in the latest world (`invokelatest`): it cannot be a fact"
    k === :inference && return "a result decided by inference (`return_type`): declare the type"
    k === :closure && return "a closure handed to the runtime"
    return "a call the compiler dispatches at run time"
end

function Base.show(io::IO, ::MIME"text/plain", r::FullyTypedReport)
    sig = r.entry
    if isfullytyped(r)
        print(io, "fully typed: ", sig, "\n  every call on a normal path is at a fact signature",
              r.dynamic == 0 ? "" : " ($(r.dynamic) declared dynamic site$(r.dynamic == 1 ? "" : "s"))")
        return
    end
    n = length(r.sites)
    print(io, "not fully typed: ", sig, "\n  ", n, " run-time site", n == 1 ? "" : "s",
          " on normal paths; each pays the facts rule's cost:")
    for h in first(r.sites, 12)
        callee = h.callee isa Symbol || h.callee isa String ? string(h.callee) : sprint(show, h.callee)
        print(io, "\n  ", h.line, ": ", callee, "(", join(map(string, h.argtypes isa AbstractVector ? h.argtypes : Any[]), ", "), ")",
              "  in ", h.caller.def isa Method ? h.caller.def.name : h.caller,
              "\n      ", _site_hint(h))
    end
    n > 12 && print(io, "\n  … ", n - 12, " more")
end
Base.show(io::IO, r::FullyTypedReport) = print(io, isfullytyped(r) ? "FullyTypedReport(fully typed)" : "FullyTypedReport($(length(r.sites)) run-time sites)")

"""
    NotFullyTypedError

Raised, under `@error_on_abstract`, by a trait function whose code at a key has run-time sites on
normal paths.
"""
struct NotFullyTypedError <: Exception
    report::FullyTypedReport
end
Base.showerror(io::IO, e::NotFullyTypedError) = show(io, MIME"text/plain"(), e.report)

"The certificate of a worker signature (its function at the trait objects' types)."
_worker_certificate(@nospecialize(sig)) = fully_typed(sig.parameters[1].instance, Tuple(sig.parameters[2:end]))
