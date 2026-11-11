# Compiling ahead to a file (traits §16): `make_executable` and `make_library`. Each runs Julia's
# `juliac` build (`--trim`) in a process of its own and links its object. A build is closed
# (compiler §7.6): generic code is compiled for the members the program declares.

# A build's own process loads the program's file. Where that file calls `make_executable` or
# `make_library` itself, the call does nothing there: a script may build its own functions.
_in_build() = ccall(:jl_generating_output, Cint, ()) != 0

"A build that failed: the build's own report, as it printed it."
struct BuildError <: Exception
    what::String
    log::String
end
function Base.showerror(io::IO, e::BuildError)
    print(io, "BuildError: ", e.what)
    isempty(e.log) || print(io, "\n", e.log)
end

# the build script of `juliac`: an installed Julia has it under share/julia/juliac, a source build
# in its tree
function _juliac_buildscript()
    for p in (joinpath(Sys.BINDIR, Base.DATAROOTDIR, "julia", "juliac", "juliac-buildscript.jl"),
              joinpath(Sys.BINDIR, "..", "..", "test", "trimming", "juliac-buildscript.jl"),
              joinpath(Sys.BINDIR, "..", "..", "contrib", "juliac", "juliac-buildscript.jl"))
        isfile(p) && return abspath(p)
    end
    throw(BuildError("this Julia has no `juliac` build script (looked under $(Sys.BINDIR))", ""))
end

# where a function is written, for the build's process to load it: a file included into `Main`, or a
# package's module
function _source_of(@nospecialize(f), @nospecialize(tt))
    ms = methods(f, tt)
    isempty(ms) && throw(ArgumentError("$f has no method at $tt"))
    m = first(ms)
    mod = m.module
    root = Base.moduleroot(mod)
    name = nameof(f)
    (isdefined(mod, name) && getglobal(mod, name) === f) || throw(ArgumentError(
        "a build takes a function its process can name: $f is no global function of $mod (an anonymous function, a closure)"))
    if root === Main
        file = string(m.file)
        isfile(file) || throw(ArgumentError(
            "$f is defined at the prompt ($file): a build's process loads its program from a file or a package. " *
            "Write it to a file and `include` it"))
        mod === Main || throw(ArgumentError("$f is defined in $mod, a module of `Main`: a build takes a function of `Main` or of a package"))
        return (:file, abspath(file), nameof(f))
    end
    return (:package, Base.PkgId(root), (fullname(mod)..., nameof(f)))
end

_c_compatible(@nospecialize(T)) =
    T === Nothing || T === Cvoid || T === Cstring || T === Cwstring || (T isa DataType && T <: Ptr) ||
    (isbitstype(T) && T !== Union{})

function _load_lines(srcs)
    lines = String[]
    for s in unique(srcs)
        if s[1] === :file
            push!(lines, "include($(repr(s[2])))")
        else
            pkg = s[2]::Base.PkgId
            push!(lines, "const $(pkg.name) = Base.require(Base.PkgId(Base.UUID($(repr(string(pkg.uuid)))), $(repr(pkg.name))))")
        end
    end
    return unique(lines)
end
_ref(s) = s[1] === :file ? "Main.$(s[3])" : join(string.(s[3]), ".")

function _run_build(driver::String, out::String, kind::Symbol; project, trim::Symbol, keep::Bool)
    dir = dirname(driver)
    obj = joinpath(dir, "program-o.a")
    log = joinpath(dir, "build.log")
    julia = joinpath(Sys.BINDIR, Base.julia_exename())
    lib = abspath(joinpath(Sys.BINDIR, "..", "lib"))
    sysimg = unsafe_string(Base.JLOptions().image_file)
    cmd = `$julia -t 1 -J $sysimg --startup-file=no --history-file=no --project=$project
           --output-o $obj --output-incremental=no --strip-ir --strip-metadata --experimental
           --trim=$(replace(string(trim), "_" => "-")) $(_juliac_buildscript()) $driver
           $(kind === :exe ? "--output-exe" : "--output-lib") true`
    ok = success(pipeline(ignorestatus(cmd); stdout = log, stderr = log))
    text = read(log, String)
    if !ok || !isfile(obj)
        n = count("\nError #", "\n" * text)
        what = n > 0 ? "the build refuses $n call$(n == 1 ? "" : "s") it cannot resolve; the program is not fully typed there" :
                       "the build's process failed"
        keep || rm(dir; recursive = true, force = true)
        throw(BuildError(what, text))
    end
    cfg = joinpath(Sys.BINDIR, Base.DATAROOTDIR, "julia", "julia-config.jl")
    flags = split(read(`$julia --startup-file=no $cfg --ldflags --ldlibs`, String))
    cc = get(ENV, "CC", "cc")
    link = kind === :exe ?
        `$cc -o $out -Wl,--whole-archive $obj -Wl,--no-whole-archive -lm -L$lib -L$(joinpath(lib, "julia")) -Wl,-rpath,$lib -Wl,-rpath,$(joinpath(lib, "julia")) $flags -ljulia-internal` :
        `$cc -shared -o $out -Wl,--whole-archive $obj -Wl,--no-whole-archive -lm -L$lib -L$(joinpath(lib, "julia")) -Wl,-rpath,$lib -Wl,-rpath,$(joinpath(lib, "julia")) $flags -ljulia-internal`
    lok = success(pipeline(ignorestatus(link); stdout = log, stderr = log, append = true))
    lok && isfile(out) || (t = read(log, String); keep || rm(dir; recursive = true, force = true);
                           throw(BuildError("linking failed", t)))
    keep || rm(dir; recursive = true, force = true)
    return out
end

"""
    make_executable(main, path; project = Base.active_project(), trim = :safe, keep = false) -> path

Write an executable of `main(args::Vector{String})` at `path` (traits §16), by `juliac --trim`. The
build is closed: generic code at traits is compiled for the members the program declares. A program
whose calls are all resolved when compiled gives a binary without a compiler in it; a call the build
cannot resolve raises `BuildError` with the build's report. `main` is a function of `Main` written in
a file, or of a package. `trim` is `:safe` or `:unsafe_warn`; `keep` keeps the build's directory.
"""
function make_executable(@nospecialize(main), path::AbstractString; project = Base.active_project(),
                         trim::Symbol = :safe, keep::Bool = false)
    _in_build() && return abspath(path)
    hasmethod(main, Tuple{Vector{String}}) ||
        throw(ArgumentError("make_executable takes a function with a method `main(args::Vector{String})`"))
    rt = Base.infer_return_type(main, Tuple{Vector{String}})
    rt <: Union{Integer,Nothing} && rt !== Union{} ||
        throw(ArgumentError("`main(args::Vector{String})` returns an exit code, an integer; it infers $rt"))
    src = _source_of(main, Tuple{Vector{String}})
    dir = mktempdir(; cleanup = false)
    driver = joinpath(dir, "driver.jl")
    open(driver, "w") do io
        foreach(l -> println(io, l), _load_lines([src]))
        # `juliac` builds `Main.main`, marked as the program's entry
        if src[1] === :file && src[3] === :main
            println(io, "(@main)")
        else
            println(io, "const __program_main = ", _ref(src))
            println(io, "function (@main)(args::Vector{String})::Cint\n    r = __program_main(args)\n    return r === nothing ? Cint(0) : Cint(r)\nend")
        end
    end
    return _run_build(driver, abspath(path), :exe; project, trim, keep)
end

"""
    make_library(functions, path; project = Base.active_project(), trim = :safe, keep = false) -> path

Write a shared library at `path` (traits §16) that exports each function of `functions` under its
name, with C's calling convention. `functions` lists `f => (R, (A...))`: the function, its result
type and its argument types, each a type C can pass (a bits type, a pointer, `Cstring`, `Nothing`).
Each function is one of `Main` written in a file, or of a package. Built as `make_executable` builds.
"""
function make_library(functions, path::AbstractString; project = Base.active_project(),
                      trim::Symbol = :safe, keep::Bool = false)
    _in_build() && return abspath(path)
    srcs = Any[]
    decls = String[]
    for (f, sig) in functions
        R, A = sig
        A isa Tuple || throw(ArgumentError("$f => (R, (A...)): the argument types as a tuple"))
        for T in (R, A...)
            _c_compatible(T) || throw(ArgumentError("$f: $T cannot be passed to or from C"))
        end
        hasmethod(f, Tuple{A...}) || throw(ArgumentError("$f has no method at $(Tuple{A...})"))
        rt = Base.infer_return_type(f, Tuple{A...})
        rt <: R || throw(ArgumentError("$f at $(Tuple{A...}) infers its result as $rt, declared $R"))
        s = _source_of(f, Tuple{A...})
        push!(srcs, s)
        name = string(s[1] === :file ? s[3] : last(s[3]))
        push!(decls, "Base._ccallable($(repr(name)), $R, Tuple{typeof($(_ref(s))), $(join(string.(A), ", "))$(isempty(A) ? "" : ",")})")
    end
    isempty(decls) && throw(ArgumentError("make_library takes at least one function"))
    dir = mktempdir(; cleanup = false)
    driver = joinpath(dir, "driver.jl")
    open(driver, "w") do io
        foreach(l -> println(io, l), _load_lines(srcs))
        foreach(l -> println(io, l), decls)
    end
    return _run_build(driver, abspath(path), :lib; project, trim, keep)
end
