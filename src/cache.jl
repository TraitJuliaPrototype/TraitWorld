# The cache across sessions (W-62; `writeup/plans/2026-10-27-session-cache.md` in the design repository).
# What a session compiles is recorded at exit; a builder, one per environment, makes package images of it
# ("parts", one per dependency set); later sessions load each part once its dependencies are loaded. On with
# JULIA_TW_CACHE=1; never in a process that generates output (an image records the modules loaded while it is
# built, so a part loaded there would make that image stale at every rebuild).
#
# The directory, per environment key (`_cache_key`): `parts/` (the generated packages, an implicit environment),
# `index.txt` (the parts published, replaced by a rename), `store.jls` (the entries kept), `records/` (sessions'
# records not yet merged), `known.txt` (the entries' hashes, read at exit), `build.lock`, `build.log`.

const _CACHE_ON = Ref(false)
const _CACHE_DIR = Ref("")
"The runtime's newly-inferred list: every CodeInstance cached after TraitWorld's init."
const _CACHE_NEW = Any[]
"The parts published and not yet loaded, with the packages each waits for."
const _CACHE_PARTS = Tuple{Base.PkgId,Vector{Base.PkgId}}[]
const _CACHE_LOADING = Ref(false)
"What the cache did in this session: parts loaded and skipped (stale images), time loading them."
const _CACHE_STATS = Dict{Symbol,Float64}()

_cache_root() = get(ENV, "JULIA_TW_CACHE_DIR", joinpath(first(DEPOT_PATH), "tw-cache"))

"""
The environment's key: every project, manifest and preference file of the load path, and the Julia build
with its system image. Not the load order. A dev'd package's edit makes its image new; the parts that depend
on it are stale and skipped until the builder makes them again.
"""
function _cache_key()
    h = hash(Base.GIT_VERSION_INFO.commit_short)
    img = unsafe_string(Base.JLOptions().image_file)
    h = hash(img, hash(isfile(img) ? mtime(img) : 0.0, h))
    for env in Base.load_path()
        isfile(env) || continue
        h = hash(read(env), h)
        man = Base.project_file_manifest_path(env)
        man isa String && isfile(man) && (h = hash(read(man), h))
        prefs = joinpath(dirname(env), "LocalPreferences.toml")
        isfile(prefs) && (h = hash(read(prefs), h))
    end
    return string(h; base = 16)
end

function _cache_init!()
    _CACHE_ON[] = get(ENV, "JULIA_TW_CACHE", "0") == "1" && ccall(:jl_generating_output, Cint, ()) == 0
    _CACHE_ON[] || return nothing
    t = time()
    dir = joinpath(_cache_root(), _cache_key())
    _CACHE_DIR[] = dir
    empty!(_CACHE_NEW)
    ccall(:jl_set_newly_inferred, Cvoid, (Any,), _CACHE_NEW)
    atexit(_cache_at_exit)
    _cache_read_index!(dir)
    _CACHE_STATS[:init] = time() - t
    return nothing
end

function _cache_read_index!(dir::String)
    empty!(_CACHE_PARTS)
    f = joinpath(dir, "index.txt")
    isfile(f) || return nothing
    for line in eachline(f)
        fs = split(line, '\t')
        length(fs) >= 2 || continue
        deps = Base.PkgId[]
        length(fs) >= 3 && for d in split(fs[3], ';'; keepempty = false)
            u, n = split(d, '=')
            push!(deps, Base.PkgId(Base.UUID(u), String(n)))
        end
        push!(_CACHE_PARTS, (Base.PkgId(Base.UUID(fs[2]), String(fs[1])), deps))
    end
    return nothing
end

"""
Load the parts whose packages are all loaded, from the package callback. A part whose image is not fresh
(a dependency changed since the builder made it) is skipped: a session never compiles a part.
"""
function _cache_load_ready!()
    (_CACHE_ON[] && !_CACHE_LOADING[] && !isempty(_CACHE_PARTS)) || return nothing
    ready = Base.PkgId[]
    for (id, deps) in _CACHE_PARTS
        all(d -> haskey(Base.loaded_modules, d), deps) && push!(ready, id)
    end
    isempty(ready) && return nothing
    filter!(p -> !(p[1] in ready), _CACHE_PARTS)
    _CACHE_LOADING[] = true
    parts = joinpath(_CACHE_DIR[], "parts")
    push!(LOAD_PATH, parts)
    # the callback runs inside a `require`, whose cache of the load path predates the push
    outer = Base.LOADING_CACHE[]
    Base.LOADING_CACHE[] = nothing
    t = time()
    try
        for id in ready
            if Base.isprecompiled(id)
                try
                    Base.require(id)
                    _CACHE_STATS[:loaded] = get(_CACHE_STATS, :loaded, 0.0) + 1
                catch err
                    _CACHE_STATS[:failed] = get(_CACHE_STATS, :failed, 0.0) + 1
                    @debug "TraitWorld cache: part not loaded" id exception = err
                end
            else
                _CACHE_STATS[:stale] = get(_CACHE_STATS, :stale, 0.0) + 1
            end
        end
    finally
        filter!(!=(parts), LOAD_PATH)
        Base.LOADING_CACHE[] = outer
        _CACHE_LOADING[] = false
        _CACHE_STATS[:load] = get(_CACHE_STATS, :load, 0.0) + (time() - t)
    end
    return nothing
end

# ---- recording, at exit ----

"The packages a session's code can be kept for: those loaded from images (not `Main`, not the cache's parts)."
function _cache_image_modules()
    mods = IdDict{Module,Base.PkgId}()
    for (id, m) in Base.loaded_modules
        (id.name == "Main" || startswith(id.name, "TWC_")) && continue
        mods[m] = id
    end
    return mods
end

"Add the packages `x` names to `deps`; false when it names a module of the session (no later session has it)."
function _cache_deps!(deps::Set{Base.PkgId}, @nospecialize(x), mods::IdDict{Module,Base.PkgId})
    if x isa Module
        id = get(mods, Base.moduleroot(x), nothing)
        id === nothing && return false
        id.name in ("Core", "Base") || push!(deps, id)
        return true
    elseif x isa Union
        return _cache_deps!(deps, x.a, mods) && _cache_deps!(deps, x.b, mods)
    elseif x isa UnionAll
        return _cache_deps!(deps, x.var, mods) && _cache_deps!(deps, x.body, mods)
    elseif x isa TypeVar
        return _cache_deps!(deps, x.lb, mods) && _cache_deps!(deps, x.ub, mods)
    elseif x isa Core.TypeofVararg
        return !isdefined(x, :T) || _cache_deps!(deps, x.T, mods)
    elseif x isa DataType
        _cache_deps!(deps, x.name.module, mods) || return false
        for p in x.parameters
            _cache_deps!(deps, p, mods) || return false
        end
        return true
    elseif x isa Union{Symbol,Number,Char,Nothing,String}
        return true
    elseif x isa Tuple
        return all(p -> _cache_deps!(deps, p, mods), x)
    else
        return _cache_deps!(deps, typeof(x), mods)
    end
end

"The packages a CodeInstance's code reached: the modules of the methods its edges name (M3: extensions' code)."
function _cache_edge_deps!(deps::Set{Base.PkgId}, ci::Core.CodeInstance, mods::IdDict{Module,Base.PkgId})
    isdefined(ci, :edges) || return nothing
    for e in ci.edges
        m = e isa Core.CodeInstance ? (e.def isa Core.MethodInstance ? e.def.def : e.def.def.def) :
            e isa Core.MethodInstance ? e.def :
            e isa Method ? e : nothing
        m isa Method || continue
        id = get(mods, Base.moduleroot(m.module), nothing)
        id === nothing || id.name in ("Core", "Base") || push!(deps, id)   # an edge into the session's code: kept, validated at load
    end
    return nothing
end

_cache_blob(kind::Symbol, @nospecialize(T)) = (io = IOBuffer(); Serialization.serialize(io, (kind, T)); take!(io))

"The session's entries: (hash, blob, dependencies) for each CodeInstance and check that a later session can have."
function _cache_entries()
    mods = _cache_image_modules()
    out = Tuple{UInt64,Vector{UInt8},Vector{Base.PkgId}}[]
    seen = Set{UInt64}()
    add!(kind, T, deps) = begin
        b = try _cache_blob(kind, T) catch; return end
        h = hash(b)
        h in seen && return
        push!(seen, h)
        push!(out, (h, b, sort!(collect(deps); by = string)))
    end
    for ci in _CACHE_NEW
        ci isa Core.CodeInstance || continue
        (ci.owner === nothing || ci.owner === :facts) || continue
        ci.max_world == typemax(UInt) || continue                  # invalidated in the session
        mi = ci.def isa Core.MethodInstance ? ci.def : ci.def.def
        m = mi.def
        m isa Method || continue
        deps = Set{Base.PkgId}()
        (_cache_deps!(deps, m.module, mods) && _cache_deps!(deps, mi.specTypes, mods)) || continue
        _cache_edge_deps!(deps, ci, mods)
        add!(ci.owner === :facts ? :facts : :plain, mi.specTypes, deps)
    end
    for sig in _CHECKED_IN_SESSION                                 # the first-call checks: kept as checked ahead
        deps = Set{Base.PkgId}()
        _cache_deps!(deps, sig, mods) || continue
        add!(:check, sig, deps)
    end
    return out
end

function _cache_known(dir::String)
    f = joinpath(dir, "known.txt")
    s = Set{UInt64}()
    isfile(f) && for l in eachline(f)
        isempty(l) || push!(s, parse(UInt64, l; base = 16))
    end
    return s
end

"What the builder needs of a package: its name, its image (for its dependencies) and an extension's parent and triggers."
function _cache_pkg_info(id::Base.PkgId)
    o = get(Base.pkgorigins, id, nothing)
    cp = o === nothing || o.cachepath === nothing ? "" : o.cachepath
    ext = [string(p.uuid, '=', p.name) for p in get(Base.EXT_PRIMED, id, Base.PkgId[])]
    return (name = id.name, cachepath = cp, ext = ext)
end

"Record the session's entries that the cache does not have yet in `dir/records`; the number of them."
function _cache_record(dir::String)
    entries = _cache_entries()
    known = _cache_known(dir)
    new = count(e -> !(e[1] in known), entries)
    new > 0 || return (length(entries), 0)
    pkgs = Dict{String,Any}()
    for e in entries, d in e[3]
        haskey(pkgs, string(d.uuid)) || (pkgs[string(d.uuid)] = _cache_pkg_info(d))
    end
    rec = (entries = [(e[1], e[2], [string(d.uuid, '=', d.name) for d in e[3]]) for e in entries if !(e[1] in known)],
           pkgs = pkgs)
    mkpath(joinpath(dir, "records"))
    f = joinpath(dir, "records", string(getpid(), '-', round(Int, time() * 1000), ".jls"))
    Serialization.serialize(f * ".tmp", rec)
    mv(f * ".tmp", f; force = true)
    return (length(entries), new)
end

function _cache_at_exit()
    _CACHE_ON[] || return nothing
    ccall(:jl_set_newly_inferred, Cvoid, (Any,), nothing)
    try
        t = time()
        n, new = _cache_record(_CACHE_DIR[])
        get(ENV, "JULIA_TW_CACHE_REPORT", "0") == "1" &&
            println(stderr, "TraitWorld cache: recorded ", n, " entries, ", new, " new, in ",
                    round(time() - t; digits = 3), " s; this session ", _CACHE_STATS)
        new > 0 && _cache_start_builder(_CACHE_DIR[])
    catch err
        println(stderr, "TraitWorld cache: not recorded: ", sprint(showerror, err))
    end
    return nothing
end

"""
Start the builder: in the background (detached, it outlives the session), synchronously with
JULIA_TW_CACHE_BUILD=sync, or not at all with =off (the records wait for the next builder).
"""
function _cache_start_builder(dir::String)
    mode = get(ENV, "JULIA_TW_CACHE_BUILD", "background")
    mode == "off" && return nothing
    proj = Base.active_project()
    # the session's flags, but images with native code: a session run with --pkgimages=existing would make
    # parts without it, and every session would generate their code again
    jl = filter(a -> !startswith(a, "--pkgimages") && !startswith(a, "--compiled-modules"), Base.julia_cmd().exec)
    cmd = `$jl --pkgimages=yes --compiled-modules=yes --startup-file=no --project=$(proj === nothing ? "@." : proj) -e "using TraitWorld; TraitWorld._cache_build(ARGS[1])" $dir`
    env = copy(ENV)
    env["JULIA_TW_CACHE"] = "0"
    env["JULIA_DEPOT_PATH"] = join(DEPOT_PATH, Sys.iswindows() ? ';' : ':')
    env["JULIA_LOAD_PATH"] = join(LOAD_PATH, Sys.iswindows() ? ';' : ':')
    cmd = setenv(cmd, env)
    log = joinpath(dir, "build.log")
    if mode == "sync"
        run(pipeline(cmd; stdout = log, stderr = log, append = true))
    else
        run(pipeline(detach(cmd); stdout = log, stderr = log, append = true); wait = false)
    end
    return nothing
end

# ---- the builder, in its own process ----

function _cache_trylock(f::String)
    for _ in 1:2
        try
            io = Base.Filesystem.open(f, Base.Filesystem.JL_O_CREAT | Base.Filesystem.JL_O_EXCL | Base.Filesystem.JL_O_WRONLY, 0o644)
            write(io, string(getpid()))
            close(io)
            return true
        catch err
            err isa Base.IOError || rethrow()
            time() - mtime(f) > 3600 ? rm(f; force = true) : return false   # a builder that died
        end
    end
    return false
end

_cache_id(s::AbstractString) = (u = split(s, '='); Base.PkgId(Base.UUID(u[1]), String(u[2])))

"Each package's dependencies, transitively, from the headers of the images the sessions loaded."
function _cache_closure(pkgs::Dict{String,Any})
    direct = Dict{Base.PkgId,Vector{Base.PkgId}}()
    for (u, info) in pkgs
        id = Base.PkgId(Base.UUID(u), info.name)
        ds = Base.PkgId[]
        if !isempty(info.cachepath) && isfile(info.cachepath)
            try
                _, (_, _, requires), required = Base.parse_cache_header(info.cachepath)
                foreach(r -> push!(ds, r.second), requires)
                foreach(r -> push!(ds, r.first), required)
            catch
            end
        end
        foreach(s -> push!(ds, _cache_id(s)), info.ext)
        direct[id] = unique!(ds)
    end
    closure = Dict{Base.PkgId,Set{Base.PkgId}}()
    function walk(id)
        haskey(closure, id) && return closure[id]
        s = closure[id] = Set{Base.PkgId}()
        for d in get(direct, id, Base.PkgId[])
            d == id && continue
            push!(s, d)
            union!(s, walk(d))
        end
        return s
    end
    foreach(walk, collect(keys(direct)))
    return closure
end

"The packages a part waits for and imports: the entry's dependencies none of the others depend on."
function _cache_antichain(deps::Vector{Base.PkgId}, closure)
    return sort!([p for p in deps if !any(q -> q != p && p in get(closure, q, ()), deps)]; by = string)
end

"""
    _cache_build(dir)

The builder: merge the sessions' records into the store, make one part per dependency set, precompile the parts
that are new or stale, then publish the index by a rename. One builder per environment (the lock file); a session
that starts meanwhile loads the parts of the previous index.
"""
function _cache_build(dir::String)
    lock = joinpath(dir, "build.lock")
    _cache_trylock(lock) || (println("builder: another builder holds the lock"); return nothing)
    t0 = time()
    try
        storef = joinpath(dir, "store.jls")
        store = isfile(storef) ? Serialization.deserialize(storef) :
            (entries = Dict{UInt64,Tuple{Vector{UInt8},Vector{String}}}(), pkgs = Dict{String,Any}())
        recs = filter(f -> endswith(f, ".jls"), readdir(joinpath(dir, "records"); join = true))
        for f in recs
            r = try Serialization.deserialize(f) catch; continue end
            for (h, b, deps) in r.entries
                store.entries[h] = (b, deps)
            end
            merge!(store.pkgs, r.pkgs)
        end
        Serialization.serialize(storef * ".tmp", store)
        mv(storef * ".tmp", storef; force = true)
        foreach(f -> rm(f; force = true), recs)

        closure = _cache_closure(store.pkgs)
        exts = Dict{Base.PkgId,Vector{Base.PkgId}}()
        for (u, info) in store.pkgs
            isempty(info.ext) || (exts[Base.PkgId(Base.UUID(u), info.name)] = _cache_id.(info.ext))
        end
        groups = Dict{Vector{Base.PkgId},Vector{UInt64}}()
        for (h, (_, deps)) in store.entries
            push!(get!(groups, _cache_antichain(_cache_id.(deps), closure), UInt64[]), h)
        end
        parts = joinpath(dir, "parts")
        mkpath(parts)
        tw = Base.PkgId(@__MODULE__)
        index = String[]
        push!(LOAD_PATH, parts)
        built = 0; failed = 0
        for (key, hs) in groups
            sort!(hs)
            name = string("TWC_", string(hash(string.(key)); base = 16), "_", string(hash(hs); base = 16)[1:min(end, 8)])
            uuid = Base.uuid5(Base.UUID("6a8b5b4e-60a6-4a77-9a9d-0b3d2a1a7c11"), name)
            # an extension is not imported by name: its parent and triggers are, and Julia loads it
            imports = unique!(sort!(vcat([get(exts, p, [p]) for p in key]...); by = string))
            filter!(!=(tw), imports)
            pdir = joinpath(parts, name)
            if !isdir(pdir)
                mkpath(joinpath(pdir, "src"))
                open(joinpath(pdir, "Project.toml"), "w") do io
                    println(io, "name = \"", name, "\"\nuuid = \"", uuid, "\"\nversion = \"0.0.1\"\n\n[deps]")
                    println(io, tw.name, " = \"", tw.uuid, "\"")
                    foreach(p -> println(io, p.name, " = \"", p.uuid, "\""), imports)
                end
                Serialization.serialize(joinpath(pdir, "src", "entries.jls"), [store.entries[h][1] for h in hs])
                open(joinpath(pdir, "src", name * ".jl"), "w") do io
                    println(io, "# A part of TraitWorld's cache across sessions, generated by its builder: the code sessions compiled,")
                    println(io, "# for these packages, compiled again into this image.")
                    println(io, "module ", name)
                    println(io, "import ", join([tw.name; [p.name for p in imports]], ", "))
                    println(io, "include_dependency(joinpath(@__DIR__, \"entries.jls\"))")
                    println(io, "const COUNTS = TraitWorld._cache_replay(@__MODULE__, joinpath(@__DIR__, \"entries.jls\"))")
                    println(io, "end")
                end
            end
            id = Base.PkgId(uuid, name)
            ok = Base.isprecompiled(id) || try
                Base.compilecache(id)
                built += 1
                true
            catch err
                println("builder: ", name, " not built: ", sprint(showerror, err)[1:min(end, 400)])
                failed += 1
                false
            end
            ok && push!(index, string(name, '\t', uuid, '\t', join([string(p.uuid, '=', p.name) for p in key], ';')))
        end
        filter!(!=(parts), LOAD_PATH)
        f = joinpath(dir, "index.txt")
        write(f * ".tmp", join(index, '\n'), isempty(index) ? "" : "\n")
        mv(f * ".tmp", f; force = true)
        write(joinpath(dir, "known.txt"), join([string(h; base = 16) for h in keys(store.entries)], '\n'))
        # parts no longer published: their sources and images (a session that loaded one keeps it)
        live = Set(first.(split.(index, '\t')))
        for p in readdir(parts)
            p in live && continue
            rm(joinpath(parts, p); recursive = true, force = true)
            rm(joinpath(first(DEPOT_PATH), "compiled", "v$(VERSION.major).$(VERSION.minor)", p); recursive = true, force = true)
        end
        println("builder: ", length(store.entries), " entries, ", length(groups), " parts (", built, " built, ", failed,
                " failed) in ", round(time() - t0; digits = 1), " s")
    finally
        rm(lock; force = true)
    end
    return nothing
end

# ---- in a part's image, while it is built ----

"Compile `T`'s method instance for the facts owner: code the session compiled by facts is kept as that owner's (E-175)."
function _cache_compile_facts(@nospecialize(T))
    w = Base.get_world_counter()
    ms = Base._methods_by_ftype(T, 1, w)
    (ms isa Vector && length(ms) == 1) || return false
    mi = Base.Compiler.specialize_method(ms[1])
    ci = Base.Compiler.typeinf_ext_toplevel(mi, w, Base.Compiler.SOURCE_MODE_ABI, Base.Compiler.TRIM_NO, Base.Compiler.FACTS_OWNER)
    return ci !== nothing
end

"""
Compile a part's entries into the image being built: plain code by `precompile`, facts code for the facts owner,
and the first-call checks run and kept as checked ahead. An entry that no longer applies (a type gone, a check
that fails now) is counted and left out.
"""
function _cache_replay(mod::Module, file::String)
    ok = 0; failed = 0
    for b in Serialization.deserialize(file)::Vector{Vector{UInt8}}
        r = try
            kind, T = Serialization.deserialize(IOBuffer(b))
            kind === :plain ? precompile(T) :
            kind === :facts ? _cache_compile_facts(T) :
            kind === :check ? (_check_ahead!(mod, nothing, T); true) : false
        catch
            false
        end
        r === true ? (ok += 1) : (failed += 1)
    end
    return (ok = ok, failed = failed)
end
