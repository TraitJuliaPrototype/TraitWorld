# ---------------------------------------------------------------------------
# Sealing (writeup/poc3-plan.md §3.3 and §9.3), the stock-Julia approximation.
#
# Julia is sealed as soon as traits are in effect (BaseInterface is implicit);
# a loaded trait package seals itself; a loaded interface package seals itself
# and the dependency closure of the package it wraps, read from the active
# manifest. A pirate of the sealed region is a method whose definer owns
# neither the function nor a type in some signature it applies to, while every
# owner there is sealed (rule 5; delegates and declared implementers count as
# owners). The package callback looks for pirates after each top-level
# `using`, over the methods defined since the previous scan, and over all of
# them after a new seal, so a pirate that loaded first is found at the seal's
# load. Base swallows exceptions thrown by package callbacks, so the load
# itself cannot be refused: in `:refuse` mode the pirate's methods are deleted
# and a `PiracyError` is reported through the error log; in `:warn` mode, the
# interim and the default, they are reported and kept, and the audit of
# `audit.jl` warns at the first call of a worker that reaches one. Tolerated
# packages (`[traits] tolerate` of the active project and of the loaded
# interface packages) are never touched.
# ---------------------------------------------------------------------------

"Owners whose functions and types are sealed: package names, and \"Julia\"."
const SEALED = Set{String}(["Julia"])
const SEAL_MODE = Ref(:warn)
const _SCAN_WORLD = Ref{UInt}(0)      # methods whose primary_world is at most this were scanned
const _RESCAN = Ref(true)             # a seal was added: the next scan covers every method
"Packages reported as pirates once already (warn mode reports each once)."
const _REPORTED = Set{String}()

"""
    piracy_mode!(:refuse | :warn)

What a load that brings a pirate of a sealed package gets: `:refuse` deletes
the pirate's methods and reports a `PiracyError`; `:warn`, the interim and
the default, reports and keeps them (plain Julia, with the audit's warnings).
Also settable at startup with the environment variable `JULIA_TRAITWORLD_SEAL`.
"""
function piracy_mode!(m::Symbol)
    m in (:refuse, :warn) || throw(ArgumentError("piracy mode must be :refuse or :warn, got :$m"))
    SEAL_MODE[] = m
    return m
end

_owner_name(@nospecialize(o)) = o === :Julia ? "Julia" : String(nameof(o::Module))

"""
Seal an owner; `true` if it was not sealed before. A trait package needs no
rescan of the methods loaded before it: nothing could have methods on its
functions or types yet. A package sealed as part of an interface's closure
may have been loaded long before, so that seal asks for a full scan.
"""
function seal!(m::Module; rescan::Bool = false)
    n = _owner_name(owner(m))
    n in SEALED && return false
    push!(SEALED, n)
    rescan && (_RESCAN[] = true)
    return true
end
function seal_name!(n::String)
    n in SEALED && return false
    push!(SEALED, n)
    _RESCAN[] = true
    return true
end

"The names in the dependency closure of package `name`, from the active manifest (the package itself included)."
function _manifest_closure(name::String)
    out = Set{String}([name])
    proj = Base.active_project()
    proj === nothing && return out
    mpath = Base.project_file_manifest_path(proj)
    (mpath === nothing || !isfile(mpath)) && return out
    toml = Base.parsed_toml(mpath)
    deps = get(toml, "deps", toml)
    deps isa Dict || return out
    stack = String[name]
    while !isempty(stack)
        n = pop!(stack)
        entries = get(deps, n, nothing)
        entries isa Vector || continue
        for e in entries
            e isa Dict || continue
            d = get(e, "deps", nothing)
            ds = d isa Dict ? collect(keys(d)) : d isa Vector ? d : String[]
            for x in ds
                x isa String || continue
                x in out && continue
                push!(out, x)
                push!(stack, x)
            end
        end
    end
    return out
end

"An interface package seals itself and the closure of the package it wraps."
function _seal_interface!(mod::Module, wrapped::Module)
    seal!(mod)
    for n in _manifest_closure(String(nameof(Base.moduleroot(wrapped))))
        (n in ("Base", "Core") || n in _stdlib_names_str()) ? seal_name!("Julia") : seal_name!(n)
    end
    return nothing
end
_stdlib_names_str() = Set{String}(String.(collect(_stdlib_names())))

"Tolerations of a Project.toml: its `[traits] tolerate` list."
function _tolerations_of(proj::AbstractString)
    out = String[]
    isfile(proj) || return out
    toml = Base.parsed_toml(proj)
    tr = get(toml, "traits", nothing)
    tr isa Dict || return out
    l = get(tr, "tolerate", nothing)
    l isa Vector || return out
    for n in l
        n isa String && push!(out, n)
    end
    return out
end

# --- the scan -----------------------------------------------------------------------

struct Pirate
    method::Method
    definer::String
    needs::Vector{String}      # the sealed owners one of which the definer would have to be
end

"Whether `m` pirates the sealed region: in some signature it applies to, the definer owns nothing and every owner is sealed."
function _pirate_of_sealed(m::Method)
    definer = owner(m.module)
    definer === :Julia && return nothing              # Julia owns its own functions
    dname = _owner_name(definer)
    dname in TOLERATED && return nothing
    _implements_exempt(m) && return nothing
    for s in _sig_alternatives(m.sig)
        os = sig_owners(s)
        definer in os && continue
        names = String[_owner_name(o) for o in os]
        all(n -> n in SEALED, names) || continue
        return Pirate(m, dname, unique!(names))
    end
    return nothing
end

"""
Every method defined after world `since`, found through the functions and
types bound in the loaded modules and their submodules (as Aqua enumerates):
`_methods_by_ftype(Tuple{Vararg{Any}})` sorts every method against every
other and took 10 s with Makie loaded, this walk 1 s. A pirate's method is
on a function or type bound somewhere, so the walk sees it.
"""
function _methods_since(since::UInt)
    out = Method[]
    seen_f = Base.IdSet{Any}()
    seen_m = Base.IdSet{Module}()
    for (_, m) in Base.loaded_modules
        _walk_methods!(out, seen_f, seen_m, m, since)
    end
    _walk_methods!(out, seen_f, seen_m, Main, since)
    return out
end
function _walk_methods!(out::Vector{Method}, seen_f, seen_m, m::Module, since::UInt)
    m in seen_m && return nothing
    push!(seen_m, m)
    for n in names(m; all = true, imported = false)
        (isdefined(m, n) && !Base.isdeprecated(m, n)) || continue
        x = getglobal(m, n)
        if x isa Module
            x !== m && parentmodule(x) === m && _walk_methods!(out, seen_f, seen_m, x, since)
        elseif x isa Function || x isa Type
            x in seen_f && continue
            push!(seen_f, x)
            ms = try methods(x) catch; continue end
            for meth in ms
                meth.primary_world > since && push!(out, meth)
            end
        end
    end
    return nothing
end

"Pirates among the methods defined since the previous scan (all methods after a new seal)."
function find_pirates!()
    world = Base.get_world_counter()
    since = _RESCAN[] ? UInt(0) : _SCAN_WORLD[]
    found = Pirate[]
    for m in _methods_since(since)
        p = _pirate_of_sealed(m)
        p === nothing || push!(found, p)
    end
    _SCAN_WORLD[] = world
    _RESCAN[] = false
    return found
end

"""
    check_no_piracy()

The sealing scan on demand, for a package's own tests (as Aqua's piracy test
is run): throws a `PiracyError` naming every pirate of the sealed region
among the loaded methods, deleting nothing.
"""
function check_no_piracy()
    _RESCAN[] = true
    found = find_pirates!()
    isempty(found) || throw(PiracyError(_pirate_report(found, :check)))
    return nothing
end

function _pirate_report(found::Vector{Pirate}, mode::Symbol)
    io = IOBuffer()
    bypkg = Dict{String,Vector{Pirate}}()
    for p in found
        push!(get!(bypkg, p.definer, Pirate[]), p)
    end
    for (d, ps) in sort!(collect(bypkg); by = first)
        print(io, d, " defines ", length(ps), length(ps) == 1 ? " method" : " methods", " on sealed functions and types it does not own:")
        for p in first(ps, 8)
            print(io, "\n    ", p.method, "  [needs ", join(p.needs, " or "), "]")
        end
        length(ps) > 8 && print(io, "\n    … ", length(ps) - 8, " more")
        print(io, "\n")
    end
    print(io, mode === :refuse ? "The methods were deleted (refuse mode); a deleted method comes back only with a restart." :
              mode === :warn ? "Kept (warn mode): trait-bound code that reaches one runs plain Julia's answer, with the audit's warning." :
              "Found by check_no_piracy.")
    print(io, " Tolerate a package in the project file, [traits] tolerate = [\"", first(keys(bypkg)), "\"], to accept its piracy.")
    return String(take!(io))
end

"After a top-level load: find the pirates of the sealed region among the new methods, and refuse or warn."
function _check_loads!()
    isempty(SEALED) && return nothing
    found = find_pirates!()
    isempty(found) && return nothing
    mode = SEAL_MODE[]
    if mode === :refuse
        for p in found
            Base.delete_method(p.method)
        end
        _bump!()
        @error sprint(showerror, PiracyError(_pirate_report(found, :refuse)))
    else
        new = filter(p -> !(p.definer in _REPORTED), found)
        for p in new
            push!(_REPORTED, p.definer)
        end
        isempty(new) || @warn sprint(showerror, PiracyError(_pirate_report(new, :warn)))
    end
    return nothing
end

"Whether a loaded package is a trait package: its root is a trait module or holds one."
function _has_trait_module(m::Module)
    isdefined(m, :__trait_module__) && return true
    for n in names(m; all = true)
        isdefined(m, n) || continue
        x = getglobal(m, n)
        x isa Module && x !== m && parentmodule(x) === m && isdefined(x, :__trait_module__) && return true
    end
    return false
end
