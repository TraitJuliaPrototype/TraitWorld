# The build's Base (traits §16; compiler §7.6). A `juliac` build replaces some of Base's and the
# standard libraries' methods by forms a closed build can compile: printing a type, `sprint`, logging,
# deprecation warnings (the build script's files `juliac-trim-base.jl` and `juliac-trim-stdlib.jl`).
# The check that answers for the build (`fully_typed`) infers against the same replacements: the
# files' method definitions are read once a session into an overlay method table, which the compiler's
# check lays over the session's methods. The session's own methods and code are not touched.

Base.Experimental.@MethodTable _BUILD_BASE

"What the session read of the build's replacements: the definitions laid over, and the statements left out."
mutable struct BuildBase
    read::Bool
    files::Vector{String}
    replaced::Vector{Any}     # (module, definition)
    left_out::Vector{Any}     # (module, statement): what an overlay cannot hold (a binding, a type's setting)
end
const _BUILD_BASE_STATE = BuildBase(false, String[], Any[], Any[])

# the files of replacements, beside the build script
function _build_base_files()
    script = try _juliac_buildscript() catch; return String[] end
    return String[f for f in (joinpath(dirname(script), "juliac-trim-base.jl"),
                              joinpath(dirname(script), "juliac-trim-stdlib.jl")) if isfile(f)]
end

_is_overlay_definition(@nospecialize(ex)) = _is_definition(Base.unwrap_macrocalls(ex)) ||
    (Meta.isexpr(Base.unwrap_macrocalls(ex), :function) && Meta.isexpr(Base.unwrap_macrocalls(ex).args[1], (:call, :where, :(::))))

# the name a definition defines, where it is a plain name
function _definition_name(@nospecialize(ex))
    sig = Base.unwrap_macrocalls(ex).args[1]
    while Meta.isexpr(sig, :where) || Meta.isexpr(sig, :(::))
        sig = sig.args[1]
    end
    return Meta.isexpr(sig, :call) ? sig.args[1] : nothing
end

# one statement of the files, written for `mod`: a method's definition goes to the overlay table
function _overlay_eval(mod::Module, @nospecialize(ex))
    st = _BUILD_BASE_STATE
    if ex isa LineNumberNode || ex === nothing
    elseif Meta.isexpr(ex, :block)
        for a in ex.args
            _overlay_eval(mod, a)
        end
    elseif ex isa Expr && _is_overlay_definition(ex)
        name = _definition_name(ex)
        try
            if name isa Symbol && !isdefined(mod, name)
                # a function the files add: it replaces nothing, and is defined as it is written
                Core.eval(mod, ex)
            else
                Core.eval(mod, Expr(:macrocall, GlobalRef(Base.Experimental, Symbol("@overlay")), LineNumberNode(0, :none),
                                    GlobalRef(@__MODULE__, :_BUILD_BASE), ex))
            end
            push!(st.replaced, (mod, ex))
        catch
            push!(st.left_out, (mod, ex))
        end
    else
        push!(st.left_out, (mod, ex))
    end
    return nothing
end

"""
The overlay method table with the build's replacements of Base's methods, read from the build
script's files at the first call in a session; `nothing` in a build's own process, while a package
is precompiled, and where this Julia has no such files.
"""
function _build_base()
    st = _BUILD_BASE_STATE
    ccall(:jl_generating_output, Cint, ()) != 0 && return nothing
    if !st.read
        st.read = true
        st.files = _build_base_files()
        for file in st.files
            # the file's `@eval Mod begin … end` is this module's: it lays the definitions over
            M = Module(:BuildBase)
            ev = GlobalRef(@__MODULE__, :_overlay_eval)
            Core.eval(M, :(macro eval(mod, ex); Expr(:call, $ev, esc(mod), esc(Expr(:quote, ex))); end))
            Core.eval(M, :(macro eval(ex); Expr(:call, $ev, $M, esc(Expr(:quote, ex))); end))
            mapexpr = ex -> (ex isa Expr && _is_overlay_definition(ex)) ? Expr(:call, ev, M, QuoteNode(ex)) : ex
            try
                Base.invokelatest(Base.include, mapexpr, M, file)
            catch err
                @warn "the build's replacements of Base could not be read; the fully typed check runs without them" file err
            end
        end
    end
    return isempty(st.replaced) ? nothing : _BUILD_BASE
end

"""
    build_base_report() -> (; files, replaced, left_out)

What the fully typed check knows of the methods a build replaces in Base (traits §16): the files
read, the definitions laid over the session's methods for the check, and the statements of the files
that are no method's definition and are left out.
"""
function build_base_report()
    _build_base()
    st = _BUILD_BASE_STATE
    return (; files = copy(st.files), replaced = copy(st.replaced), left_out = copy(st.left_out))
end
