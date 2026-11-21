# The pirate's report (traits §12.2; facts §11.1; compiler §10.2). A pirate that ends code compiled by
# facts in the deep class, code that nothing but a stakeholder's change or a pirate can end, is reported
# by default: a warning names the method, its definer and the code ended. In strict mode such a pirate is
# refused instead (strict.jl); the report is silent only by choice. It reads what the runtime keeps of the
# invalidation itself (`jl_take_deep_endings`): nothing is walked before a definition, and a definition or
# a load that ends no such code costs nothing.

const REPORT_PIRATES = Ref(true)

"""
    TraitWorld.report_pirates!(on = true)

Turn the pirate's report on or off for this session (traits §12.2). On by default; `JULIA_TW_PIRATES=0`
at start turns it off. The report names a pirate whose definition, or whose method at a package image's
load, ends code compiled by facts that only a stakeholder's change or a pirate can end.
"""
function report_pirates!(on::Bool = true)
    REPORT_PIRATES[] = on
    ccall(:jl_set_deep_endings, Cint, (Cint,), on)
    on || _take_endings()                         # what the runtime kept so far is dropped
    return nothing
end

"A pirate's report as it was given: the method or membership, its definer, the code it ended."
struct PirateReport
    method::Union{Method,PirateMembership}
    definer::Any
    sig::Any                                       # the fact a load found broken, or `nothing`
    code::Vector{Core.CodeInstance}
end

"The pirate's reports given in this session (traits §12.2), in order."
const PIRATE_REPORTS = PirateReport[]

# what the runtime kept since the last take: [kind, cause, code, ...], kind `:definition`, `:deletion`,
# `:membership` (the cause the membership's method) or `:validation` (the cause the edge that failed)
function _take_endings()
    es = ccall(:jl_take_deep_endings, Any, ())
    return es isa Vector{Any} ? es : Any[]
end

function _ended_names(code::Vector{Core.CodeInstance}, n::Int = 6)
    names = String[]
    own = 0                                  # the library's own code: counted, not named (traits §11.3)
    for ci in code
        s = _code_name(ci)
        s == "the library's own code" && (own += 1; continue)
        s in names || push!(names, s)
    end
    more = length(names) > n ? " and $(length(names) - n) more" : ""
    lib = own == 0 ? "" : string(isempty(names) ? "" : "; ", own, " of the library's own")
    return join(first(names, n), ", ") * more * lib
end

function Base.show(io::IO, r::PirateReport)
    m = r.method
    what = m isa PirateMembership ?
        "the membership of `$(_short(m.member, 40))` in `$(_short(m.trait, 40))`, declared by $(_owner_name(r.definer)), which owns neither the trait nor the type" :
        "`$(_callform(m.sig))`, defined by $(_owner_name(r.definer)) in $(m.module), " * _pirate_why(m, r.definer)
    print(io, "a pirate ended code compiled by facts that only a stakeholder's change or a pirate can end: ", what,
          r.sig === nothing ? "" : ", wins at `$(_callform(r.sig))`",
          ". It ended $(length(r.code)) instance$(length(r.code) == 1 ? "" : "s"): ", _ended_names(r.code),
          ". It is followed, as plain Julia follows it: that code is compiled again. ",
          m isa PirateMembership ?
          "The trait's owner or the type's owner declares the membership, or names the declarer a joint owner (`@joint_owners`)" :
          "Define it where a type it is for is owned, or name the definer a joint owner (`@joint_owners`)",
          "; strict mode (`TraitWorld.strict!()`) refuses such a definition; `TraitWorld.report_pirates!(false)` silences this report.")
end

# why a method is a pirate's (traits §12.2): another owner's owner-only function, or Julia's piracy
function _pirate_why(m::Method, @nospecialize(definer))
    fo = _owner_only_owner(m.sig)
    fo === nothing || return "which does not own the function: an owner-only function of $(_owner_name(fo)), whose methods are its owner's"
    return "which owns neither the function nor a type in it"
end

# the method now selected at an edge's signature, for a load's broken fact
function _selected_at(@nospecialize(s), world::UInt)
    ms = Base._methods_by_ftype(s, nothing, 1, world, false, Ref{UInt}(typemin(UInt)), Ref{UInt}(typemax(UInt)), Ptr{Int32}(C_NULL))
    (ms isa Vector && length(ms) == 1) || return nothing
    return (ms[1]::Core.MethodMatch).method
end

"""
Report the pirates among what the runtime kept of the deep code ended since the last take (traits §12.2).
A definition's or an image's method that is a pirate's, a pirate's membership, and at a load a method in
the session that breaks a fact of an image's deep code and is a pirate's there.
"""
function _report_endings!(es::Vector{Any})
    isempty(es) && return nothing
    REPORT_PIRATES[] || return nothing
    ccall(:jl_generating_output, Cint, ()) == 0 || return nothing      # an image's own build: reported at its load
    world = Base.get_world_counter()
    byc = IdDict{Any,Vector{Core.CodeInstance}}()
    order = Any[]
    sigs = IdDict{Any,Any}()
    for i in 1:3:length(es)-2
        kind, cause, ci = es[i], es[i+1], es[i+2]
        ci isa Core.CodeInstance || continue
        key = nothing
        if cause isa Method && (kind === :definition || kind === :membership)
            # a membership's cause is its method (compiler §5.6), at a declaration or an image's activation
            if _is_membership_method(cause)
                _membership_method_pirate(cause) || continue
            else
                _owned_or_julia(cause) && continue
            end
            key = cause
        elseif kind === :validation
            s = cause isa Core.MethodInstance ? cause.specTypes : cause isa Type ? cause : continue
            m = _selected_at(s, world)
            (m === nothing || _owned_or_julia(m)) && continue
            _stakeholder(owner(m.module), s) && continue
            key = m
            haskey(sigs, m) || (sigs[m] = s)
        else
            continue
        end
        v = get(byc, key, nothing)
        if v === nothing
            v = Core.CodeInstance[]
            byc[key] = v
            push!(order, key)
        end
        ci in v || push!(v, ci)
    end
    for key in order
        m = key::Method
        r = if _is_membership_method(m)
            b = Base.unwrap_unionall(m.sig)::DataType
            PirateReport(PirateMembership(_sig_arg(b.parameters[2]), _sig_arg(b.parameters[3]), m.module),
                         owner(m.module), nothing, byc[key])
        else
            PirateReport(m, owner(m.module), get(sigs, m, nothing), byc[key])
        end
        push!(PIRATE_REPORTS, r)
        @warn sprint(show, r)
    end
    return nothing
end

# After a definition (the definition hook), a declaration and a package's load: the report, by default;
# strict mode's own checks take its place where strict mode is on.
_report_now!() = (es = _take_endings(); STRICT[] || _report_endings!(es); nothing)

function _report_init!()
    on = get(ENV, "JULIA_TW_PIRATES", "1") != "0"
    REPORT_PIRATES[] = on
    ccall(:jl_set_deep_endings, Cint, (Cint,), on)
    pushfirst!(Base.package_callbacks, _report_at_load!)
    return nothing
end
_report_at_load!(_pkg = nothing) = (ccall(:jl_generating_output, Cint, ()) == 0 && _report_now!(); nothing)
