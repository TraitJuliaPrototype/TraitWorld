# ---------------------------------------------------------------------------
# View caches (rule 4): a worker compiled for a representation the library's
# image does not hold is compiled once and cached in a package of its own,
# which depends on exactly the owners of what the worker's signature names:
# the function's package, the traits' packages, the representations'
# packages. Rule 4's view says the worker sees nothing else, and sealing
# (rule 3) says nothing else may change what it sees, so the cache is keyed
# by those packages and their versions only: not by what else a session
# loads, nor by the order it loads in.
#
# Recording: `_check_once` notes each worker signature it checks (a signature
# a loaded image holds was checked when that image was built, and is not
# noted); `_enter_slow` notes each builder. Flushing (at exit, or
# `viewcache_flush`) groups the signatures by view, writes one package per
# view (`TWView_<hash>`, under `viewcache_dir()`) and precompiles it in a
# separate, niced process; its precompilation checks each signature and
# compiles `checked_call` at it. Loading: after each top-level `using`, every
# built view cache whose packages are all loaded is loaded; its signatures
# count as checked.
#
#   JULIA_TW_VIEWCACHE=0          neither record nor load
#   JULIA_TW_VIEWCACHE_DIR=<dir>  where the packages live (default: <depot>/traitworld/views)
# ---------------------------------------------------------------------------

const _VC_ON = Ref(true)
const _VC_NEW = Any[]                    # worker signatures checked in this session
const _VC_BUILDERS = Any[]               # builder call signatures built in this session
const _VC_CHECKED = Base.IdSet{Any}()    # worker signatures a loaded view cache checked when it was built
const _VC_SEEN = Set{String}()           # view caches loaded, or found not built, in this session
const _VC_STALE = String[]               # found but not built (new, or a dependency changed)

viewcache_dir() = get(ENV, "JULIA_TW_VIEWCACHE_DIR", joinpath(first(DEPOT_PATH), "traitworld", "views"))

function _vc_init!()
    _VC_ON[] = get(ENV, "JULIA_TW_VIEWCACHE", "1") != "0" && ccall(:jl_generating_output, Cint, ()) == 0
    empty!(_VC_NEW); empty!(_VC_BUILDERS); empty!(_VC_CHECKED); empty!(_VC_SEEN); empty!(_VC_STALE)
    _VC_ON[] && atexit(_vc_atexit)
    return nothing
end

@noinline function _vc_note_worker(@nospecialize(sig))
    _VC_ON[] || return nothing
    @lock _LOCK push!(_VC_NEW, sig)
    return nothing
end
@noinline function _vc_note_builder(@nospecialize(b), @nospecialize(U))
    _VC_ON[] || return nothing
    @lock _LOCK push!(_VC_BUILDERS, Tuple{typeof(b),U})
    return nothing
end

# --- the view of a signature ----------------------------------------------------

"""
The packages a signature names (root modules of its types, functions and
type parameters), without Julia's own Core, Base and compiler; `nothing` if
it names something no package can depend on: a type of a script or the REPL
(a module under `Main`), or of a package extension.
"""
function _vc_packages(@nospecialize(sig))
    roots = Base.IdSet{Module}()
    _vc_roots!(roots, sig) || return nothing
    out = Module[]
    for r in roots
        (r === Core || r === Base || r === Base.Compiler) && continue
        id = Base.PkgId(r)
        id.uuid === nothing && return nothing
        _extension_parent(r) === nothing || return nothing
        push!(out, r)
    end
    sort!(out; by = m -> String(nameof(m)))
    return out
end
function _vc_roots!(acc::Base.IdSet{Module}, @nospecialize(T))
    if T isa Union
        return _vc_roots!(acc, T.a) && _vc_roots!(acc, T.b)
    elseif T isa UnionAll
        return _vc_roots!(acc, T.var.lb) && _vc_roots!(acc, T.var.ub) && _vc_roots!(acc, T.body)
    elseif T isa Core.TypeofVararg
        return !isdefined(T, :T) || _vc_roots!(acc, T.T)
    elseif T isa TypeVar
        return _vc_roots!(acc, T.lb) && _vc_roots!(acc, T.ub)
    elseif T isa DataType
        r = Base.moduleroot(T.name.module)
        r === Main && return false
        push!(acc, r)
        for p in T.parameters
            ok = p isa Type || p isa TypeVar || p isa Core.TypeofVararg ? _vc_roots!(acc, p) :
                 p isa Tuple ? all(x -> x isa Symbol || x isa Number || _vc_roots!(acc, typeof(x)), p) :
                 p isa Symbol || p isa Number || p isa Bool ? true : _vc_roots!(acc, typeof(p))
            ok || return false
        end
    end
    return true
end

_vc_key(pkgs::Vector{Module}) = [(String(nameof(m)), string(Base.PkgId(m).uuid), string(something(pkgversion(m), v"0"))) for m in pkgs]
_vc_name(key) = "TWView_" * string(hash(key), base = 16)

"The call an entry makes for a worker signature: `checked_call`, or `checked_kwcall` for a keyword worker."
function _vc_entry_sig(@nospecialize(sig))
    ps = sig.parameters
    ps[1] === typeof(Core.kwcall) && return Tuple{typeof(checked_kwcall),ps[2:end]...}
    return Tuple{typeof(checked_call),ps...}
end

# --- flushing: write the packages, build them ---------------------------------------

_vc_atexit() = (try viewcache_flush(; wait = false) catch e; @warn "TraitWorld: writing view caches failed" exception = e; end; nothing)

"""
    viewcache_flush(; wait = true) -> Vector{String}

Write the view caches for the worker signatures checked in this session and
build them (precompile, in a niced process; `wait = false`: detached), with
those found not built. Returns the names of the caches built.
"""
function viewcache_flush(; wait::Bool = true)
    _VC_ON[] || return String[]
    groups = Dict{String,Tuple{Any,Vector{Module},Vector{Any}}}()       # name => (key, packages, signatures)
    workers = @lock _LOCK (s = copy(_VC_NEW); empty!(_VC_NEW); s)
    builders = @lock _LOCK (s = unique(_VC_BUILDERS); empty!(_VC_BUILDERS); s)
    for sig in unique(workers)
        pkgs = _vc_packages(sig)
        pkgs === nothing && continue              # a type of the session itself: not cached
        key = _vc_key(pkgs)
        name = _vc_name(key)
        push!(get!(() -> (key, pkgs, Any[]), groups, name)[3], sig)
    end
    # a builder goes with the workers whose view holds everything it names
    # (a projection onto the library's own representation needs no new worker,
    # and the conformer's image holds its builder already)
    for b in builders
        bp = _vc_packages(b)
        bp === nothing && continue
        for (_, (_, pkgs, sigs)) in groups
            all(m -> any(x -> x === m, pkgs), bp) && push!(sigs, b)
        end
    end
    d = viewcache_dir()
    tobuild = String[]
    for (name, (key, pkgs, sigs)) in groups
        _vc_write(d, name, key, pkgs, sigs) && push!(tobuild, name)
    end
    for name in _VC_STALE
        name in tobuild || push!(tobuild, name)
    end
    empty!(_VC_STALE)
    isempty(tobuild) || _vc_build(d, tobuild; wait)
    return tobuild
end

"Write (or extend) a view cache package; whether it has signatures it did not have."
function _vc_write(d, name, key, pkgs::Vector{Module}, sigs::Vector{Any})
    pdir = joinpath(d, name)
    sigfile = joinpath(pdir, "sigs.jls")
    old = Any[]
    if isfile(sigfile)
        try
            old = open(Serialization.deserialize, sigfile)::Vector{Any}
        catch
            old = Any[]                           # a type it named is gone: start again
        end
    end
    new = Any[s for s in sigs if !any(x -> x === s, old)]
    isempty(new) && return false
    mkpath(joinpath(pdir, "src"))
    tmp = sigfile * ".tmp-" * string(getpid())
    open(io -> Serialization.serialize(io, Any[old; new]), tmp, "w")
    mv(tmp, sigfile; force = true)
    h = hash(name)
    uuid = Base.UUID(UInt128(h) << 64 | UInt128(hash(h)))
    open(joinpath(pdir, "Project.toml"), "w") do io
        println(io, "name = \"", name, "\"")
        println(io, "uuid = \"", uuid, "\"")
        println(io, "version = \"0.1.0\"\n\n[deps]")
        for m in pkgs
            println(io, nameof(m), " = \"", Base.PkgId(m).uuid, "\"")
        end
        println(io, "\n[traitworld]\nview = [", join(["[\"$n\", \"$u\", \"$v\"]" for (n, u, v) in key], ", "), "]")
    end
    open(joinpath(pdir, "src", name * ".jl"), "w") do io
        println(io, "# generated by TraitWorld: compiled workers for the view of these packages (rule 4)")
        println(io, "module ", name)
        for m in pkgs
            println(io, "import ", nameof(m))     # in any order: the cache's validity does not depend on it
        end
        println(io, """
        const _SIGFILE = joinpath(@__DIR__, "..", "sigs.jls")
        include_dependency(_SIGFILE)
        const _CHECKED = TraitWorld._vc_compile(TraitWorld._vc_read(_SIGFILE))
        __init__() = TraitWorld._vc_register(_CHECKED)
        end""")
    end
    return true
end

_vc_read(f) = open(Serialization.deserialize, f)::Vector{Any}

"Run in a view cache's precompilation: check each worker signature, compile the entry's call at it; the signatures that passed."
function _vc_compile(sigs::Vector{Any})
    ccall(:jl_generating_output, Cint, ()) == 1 || return Any[]
    checked = Any[]
    for s in sigs
        if s.parameters[1] <: Builder
            precompile(s)
            continue
        end
        ok = try
            ps = Base.invokelatest(worker_problems, s)::Vector{String}
            isempty(ps) && (Base.invokelatest(_check_concrete, s); true)
        catch
            false                                 # the session's check reports it, at the call
        end
        ok || continue
        precompile(_vc_entry_sig(s)) && push!(checked, s)
    end
    return checked
end

_vc_register(sigs::Vector{Any}) = (@lock _LOCK union!(_VC_CHECKED, sigs); nothing)

function _vc_loadpath!(d)
    d in LOAD_PATH || push!(LOAD_PATH, d)
    return d
end

"Precompile view cache packages, one after the other, in a niced process of the active project."
function _vc_build(d, names::Vector{String}; wait::Bool = true)
    _vc_loadpath!(d)
    ids = [Base.PkgId(Base.UUID(Base.parsed_toml(joinpath(d, n, "Project.toml"))["uuid"]), n) for n in names]
    code = "push!(LOAD_PATH, $(repr(d))); for id in $(repr(ids)); try; Base.require(id); catch e; @error \"view cache \$(id.name)\" exception = e; end; end"
    jl = joinpath(Sys.BINDIR, Base.julia_exename())
    cmd = setenv(`nice -n 10 $jl --startup-file=no --project=$(Base.active_project()) -e $code`,
                 merge(ENV, Dict("JULIA_TW_VIEWCACHE" => "0")))
    log = joinpath(d, "build.log")
    run(pipeline(wait ? cmd : detach(cmd); stdout = log, stderr = log, append = true); wait)
    return nothing
end

# --- loading -----------------------------------------------------------------

"Load every built view cache whose packages are all loaded (after each top-level `using`)."
function _vc_load!()
    _VC_ON[] || return nothing
    d = viewcache_dir()
    isdir(d) || return nothing
    for name in readdir(d)
        startswith(name, "TWView_") || continue
        name in _VC_SEEN && continue
        f = joinpath(d, name, "Project.toml")
        isfile(f) || continue
        p = Base.parsed_toml(f)
        deps = p["deps"]::Dict{String,Any}
        all(((n, u),) -> haskey(Base.loaded_modules, Base.PkgId(Base.UUID(u::String), n)), deps) || continue
        push!(_VC_SEEN, name)
        _vc_loadpath!(d)
        id = Base.PkgId(Base.UUID(p["uuid"]::String), name)
        # called from a package callback, inside a `using` whose loading cache
        # predates the directory in LOAD_PATH: look it up without that cache
        lc = Base.LOADING_CACHE[]
        Base.LOADING_CACHE[] = nothing
        try
            if Base.isprecompiled(id)
                Base.require(id)
            else
                push!(_VC_STALE, name)            # never compiled in the session: built at exit
            end
        catch e
            @warn "TraitWorld: loading view cache $name failed" exception = e
        finally
            Base.LOADING_CACHE[] = lc
        end
    end
    return nothing
end
