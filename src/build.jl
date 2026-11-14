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

# ---- a function written at the prompt: the session's definitions, replayed by the build ----------

# the prompt's inputs of this session, in order (the REPL's history from where the session began)
function _prompt_inputs()
    repl = isdefined(Base, :active_repl) ? Base.active_repl : nothing
    (repl !== nothing && isdefined(repl, :interface)) || return nothing
    for mode in repl.interface.modes
        isdefined(mode, :hist) || continue
        hp = mode.hist
        (hasproperty(hp, :history) && hasproperty(hp, :start_idx)) || continue
        h = hp.history
        if hasproperty(hp, :modes)              # a list of texts, with their modes beside
            return String[h[i] for i in hp.start_idx+1:length(h) if hp.modes[i] === :julia]
        end
        # a list of entries, each with its mode and its text; the session's begin at `start_idx`
        return String[String(h[i].content) for i in max(1, hp.start_idx):length(h) if h[i].mode === :julia]
    end
    return nothing
end

const _DEFINING_MACROS = (Symbol("@trait"), Symbol("@implement"), Symbol("@trait_module"), Symbol("@enum"),
                          Symbol("@kwdef"), Symbol("@main"), Symbol("@ccallable"), Symbol("@joint_owners"))

# whether a top-level statement defines something a build needs: a module, a type, a function, a
# constant, an import, a trait or a membership. Anything else (a call, an assignment to a global, a
# `make_executable`) is the session's own doing and is not replayed.
function _is_session_definition(@nospecialize(ex))
    ex isa Expr || return false
    h = ex.head
    h in (:using, :import, :export, :public, :struct, :abstract, :primitive, :module, :const, :macro) && return true
    h === :function && return length(ex.args) >= 1 && !(ex.args[1] isa Expr && ex.args[1].head === :tuple)
    if h === :(=)
        l = ex.args[1]
        while l isa Expr && l.head in (:where, :(::))
            l = l.args[1]
        end
        return l isa Expr && l.head === :call
    end
    if h === :macrocall
        name = ex.args[1]
        name isa Expr && name.head === :. && (name = name.args[end]; name isa QuoteNode && (name = name.value))
        name isa GlobalRef && (name = name.name)
        name in _DEFINING_MACROS && return true
        return any(_is_session_definition, ex.args[2:end])       # `@inline f(x) = …`, a docstring on a definition
    end
    h === :call && ex.args[1] === :include && return true
    (h === :block || h === :toplevel) && return any(_is_session_definition, ex.args)
    return false
end

# the top-level statements of a session's inputs, each with its source text. Statements joined by `;`
# on one line parse as one; they are taken apart, and printed from their expressions.
function _statements(inputs::Vector{String})
    stmts = Tuple{String,Any}[]
    for input in inputs
        pos = 1
        while pos <= ncodeunits(input)
            ex, next = try Meta.parse(input, pos; greedy = true, raise = false) catch; (nothing, ncodeunits(input) + 1) end
            next > pos || break
            if ex isa Expr && ex.head === :toplevel
                for sub in ex.args
                    sub isa LineNumberNode && continue
                    push!(stmts, (string(Base.remove_linenums!(deepcopy(sub))), sub))
                end
            elseif ex !== nothing && !(ex isa Expr && ex.head in (:error, :incomplete))
                push!(stmts, (String(strip(input[pos:prevind(input, next)], [' ', '\n', ';'])), ex))
            end
            pos = next
        end
    end
    return stmts
end

"The definitions among a session's inputs, as source text, and the number of statements left out."
function _definitions(inputs::Vector{String})
    stmts = _statements(inputs)
    kept = String[t for (t, ex) in stmts if _is_session_definition(ex)]
    return kept, length(stmts) - length(kept)
end

# every symbol a statement mentions
function _symbols!(out::Set{Symbol}, @nospecialize(ex))
    if ex isa Symbol
        push!(out, ex)
    elseif ex isa QuoteNode
        ex.value isa Symbol && push!(out, ex.value)
    elseif ex isa Expr
        foreach(a -> _symbols!(out, a), ex.args)
    end
    return out
end

_defname(@nospecialize(x)) =
    x isa Symbol ? x :
    x isa Expr && x.head in (:curly, :where, :(::), :(<:), :call, :macrocall) ? _defname(x.args[x.head === :macrocall ? end : 1]) :
    x isa Expr && x.head === :. ? (x.args[end] isa QuoteNode ? x.args[end].value : nothing) : nothing

# the names a definition gives: a function's, a type's, a constant's, a module's, a trait's and its
# operations'. An import, an `include` and a membership give none.
function _defined!(out::Set{Symbol}, @nospecialize(ex))
    ex isa Expr || return out
    h = ex.head
    if h === :function || h === :macro
        n = _defname(ex.args[1]); n === nothing || push!(out, n)
    elseif h === :(=)
        n = _defname(ex.args[1]); n === nothing || push!(out, n)
    elseif h === :struct
        n = _defname(ex.args[2]); n === nothing || push!(out, n)
    elseif h === :abstract || h === :primitive || h === :module
        n = _defname(ex.args[h === :module ? 2 : 1]); n === nothing || push!(out, n)
    elseif h === :const
        foreach(a -> _defined!(out, a), ex.args)
        ex.args[1] isa Symbol && push!(out, ex.args[1])
    elseif h === :macrocall
        name = ex.args[1]
        name isa Expr && name.head === :. && (name = name.args[end]; name isa QuoteNode && (name = name.value))
        name isa GlobalRef && (name = name.name)
        args = Any[a for a in ex.args[2:end] if !(a isa LineNumberNode)]
        if name === Symbol("@trait") && !isempty(args)
            n = _defname(args[1]); n === nothing || push!(out, n)
            # a trait's operations are functions of its module
            body = length(args) >= 2 ? args[end] : nothing
            if body isa Expr && body.head === :block
                for item in body.args
                    item isa Expr || continue
                    n = _defname(item.head === :(=) ? item.args[1] : item)
                    n === nothing || push!(out, n)
                end
            end
        elseif name === Symbol("@enum") && !isempty(args)
            foreach(a -> (n = _defname(a); n === nothing || push!(out, n)), args)
        elseif name !== Symbol("@implement")
            foreach(a -> _defined!(out, a), args)
        end
    elseif h === :block || h === :toplevel
        foreach(a -> _defined!(out, a), ex.args)
    end
    return out
end

_always_replayed(@nospecialize(ex)) =
    ex isa Expr && (ex.head in (:using, :import) ||
                    (ex.head === :macrocall && _session_macro_name(ex) in (Symbol("@trait_module"), Symbol("@joint_owners"))))
function _session_macro_name(ex::Expr)
    name = ex.args[1]
    name isa Expr && name.head === :. && (name = name.args[end]; name isa QuoteNode && (name = name.value))
    name isa GlobalRef && (name = name.name)
    return name
end

"""
The definitions among a session's inputs that `root` depends on, as source text in the session's
order, and the number of statements left out. A definition is kept where it gives a name that is
needed; what it mentions is needed in turn. A membership (`@implement X S`) is kept where its type is
needed. Imports are always kept.
"""
function _needed_definitions(inputs::Vector{String}, root::Symbol)
    stmts = _statements(inputs)
    isdef = Bool[_is_session_definition(ex) for (_, ex) in stmts]
    gives = Set{Symbol}[_defined!(Set{Symbol}(), ex) for (_, ex) in stmts]
    mentions = Set{Symbol}[_symbols!(Set{Symbol}(), ex) for (_, ex) in stmts]
    keep = Bool[isdef[i] && _always_replayed(stmts[i][2]) for i in eachindex(stmts)]
    needed = Set{Symbol}((root,))
    changed = true
    while changed
        changed = false
        for i in eachindex(stmts)
            (keep[i] || !isdef[i]) && continue
            ex = stmts[i][2]
            hit = !isdisjoint(gives[i], needed)
            if !hit && ex isa Expr && ex.head === :macrocall && _session_macro_name(ex) === Symbol("@implement")
                # a membership: needed where its member type is
                args = Any[a for a in ex.args[2:end] if !(a isa LineNumberNode)]
                member = length(args) >= 2 ? _defname(args[2]) : nothing
                hit = member !== nothing && member in needed
            end
            hit || continue
            keep[i] = true
            union!(needed, mentions[i])
            changed = true
        end
    end
    return String[stmts[i][1] for i in eachindex(stmts) if keep[i]], count(!, keep)
end

# where a function is written, for the build's process to load it: a file included into `Main`, or a
# package's module
function _source_of(@nospecialize(f), @nospecialize(tt), session = nothing)
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
        if !isfile(file)
            # written at the prompt: the build replays the session's definitions
            inputs = session === nothing ? _prompt_inputs() : session
            inputs === nothing && throw(ArgumentError(
                "$f is not written in a file ($file), and this session has no prompt whose inputs a build could replay. " *
                "Write it to a file and `include` it, or pass the inputs as `session`"))
            mod === Main || throw(ArgumentError("$f is defined in $mod, a module of `Main`: a build takes a function of `Main` or of a package"))
            defs, skipped = _needed_definitions(inputs, name)
            return (:session, defs, name, skipped)
        end
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
        if s[1] === :session
            append!(lines, s[2])
        elseif s[1] === :file
            push!(lines, "include($(repr(s[2])))")
        else
            pkg = s[2]::Base.PkgId
            push!(lines, "const $(pkg.name) = Base.require(Base.PkgId(Base.UUID($(repr(string(pkg.uuid)))), $(repr(pkg.name))))")
        end
    end
    return unique(lines)
end
_ref(s) = s[1] === :package ? join(string.(s[3]), ".") : "Main.$(s[3])"

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

# A program builds exactly where its entry is fully typed (traits §14, §16): the build's check runs in
# the session first, and a program that is not fully typed is refused here, with the report.
function _check_before_build(@nospecialize(f), @nospecialize(argtypes::Tuple))
    r = fully_typed(f, argtypes)
    isfullytyped(r) && return nothing
    n = length(r.sites)
    throw(BuildError("$(nameof(f)) is not fully typed at $(Tuple{argtypes...}): a build refuses $n call$(n == 1 ? "" : "s") it cannot resolve",
                     sprint(show, MIME"text/plain"(), r)))
end

"""
    make_executable(main, path; project = Base.active_project(), trim = :safe, keep = false) -> path

Write an executable of `main(args::Vector{String})` at `path` (traits §16), by `juliac --trim`. The
build is closed: generic code at traits is compiled for the members the program declares. A program
whose calls are all resolved when compiled gives a binary without a compiler in it; a call the build
cannot resolve raises `BuildError` with the build's report. `trim` is `:safe` or `:unsafe_warn`; `keep`
keeps the build's directory.

`main` is a function of a package, or of `Main`. Written in a file, the build's process loads that
file. Written at the prompt, the build replays the definitions `main` depends on, from the prompt's
inputs, in their order: `main`'s own, and those of every function, type, constant and trait it
mentions, and so on; the memberships of the types reached; the imports. Nothing else of the session
is replayed. `session` gives the inputs in place of the prompt's history.
"""
function make_executable(@nospecialize(main), path::AbstractString; project = Base.active_project(),
                         trim::Symbol = :safe, keep::Bool = false, session = nothing)
    _in_build() && return abspath(path)
    hasmethod(main, Tuple{Vector{String}}) ||
        throw(ArgumentError("make_executable takes a function with a method `main(args::Vector{String})`"))
    rt = Base.infer_return_type(main, Tuple{Vector{String}})
    rt <: Union{Integer,Nothing} && rt !== Union{} ||
        throw(ArgumentError("`main(args::Vector{String})` returns an exit code, an integer; it infers $rt"))
    src = _source_of(main, Tuple{Vector{String}}, session)
    _check_before_build(main, (Vector{String},))
    src[1] === :session && src[4] > 0 &&
        @info "make_executable: the build replays the $(length(src[2])) definitions of the session that $(src[3]) depends on; $(src[4]) other statements are not replayed"
    dir = mktempdir(; cleanup = false)
    driver = joinpath(dir, "driver.jl")
    open(driver, "w") do io
        foreach(l -> println(io, l), _load_lines([src]))
        # `juliac` builds `Main.main`, marked as the program's entry
        if src[1] !== :package && src[3] === :main
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
                      trim::Symbol = :safe, keep::Bool = false, session = nothing)
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
        s = _source_of(f, Tuple{A...}, session)
        _check_before_build(f, A)
        push!(srcs, s)
        name = string(s[1] === :package ? last(s[3]) : s[3])
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
