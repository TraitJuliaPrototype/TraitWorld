# ---------------------------------------------------------------------------
# Stack traces show the user's code and the libraries' code, not the machinery's (note "Identical
# or error": errors name the bound). Frames of TraitWorld's own methods, and the inlined entry
# stubs next to them (generated code, `none:-1`), are removed before a backtrace is printed. The
# top frame, where the error was raised, always stays. `JULIA_TW_ALL_FRAMES=1` shows every frame.
#
# Through Base's `update_stackframes_callback` (made for Revise to correct line numbers; it edits
# the processed frames in place), chained to a callback installed before. The clean form is a
# Julia piece: a registry of modules whose frames backtraces hide, as the type printers' (piece 17).
# ---------------------------------------------------------------------------

const _PREV_FRAMES_CB = Ref{Any}(nothing)

# inlined frames carry no module of their own: those in TraitWorld's source files are its too
const _SRC_DIR = Ref{String}("")
function _is_machinery_frame(sf::Base.StackTraces.StackFrame)
    m = parentmodule(sf)
    m isa Module && Base.moduleroot(m) === TraitWorld && return true
    d = _SRC_DIR[]
    return !isempty(d) && startswith(String(sf.file), d)
end
_is_stub_frame(sf::Base.StackTraces.StackFrame) = sf.inlined && (sf.file === :none || sf.file === Symbol("./none")) && sf.line <= 0

function _hide_machinery_frames!(filtered)
    prev = _PREV_FRAMES_CB[]
    prev === nothing || try prev(filtered) catch end
    get(ENV, "JULIA_TW_ALL_FRAMES", "0") == "1" && return filtered
    filtered isa Vector{Any} || return filtered
    n = length(filtered)
    n <= 1 && return filtered
    sfs = Base.StackTraces.StackFrame[first(x) for x in filtered]
    hide = Bool[_is_machinery_frame(sf) for sf in sfs]
    # entry stubs: inlined generated frames next to a hidden frame
    for i in 1:n
        hide[i] && continue
        _is_stub_frame(sfs[i]) && ((i > 1 && hide[i-1]) || (i < n && hide[i+1])) && (hide[i] = true)
    end
    for i in 1:n                                           # a second pass: stubs between stubs
        hide[i] && continue
        _is_stub_frame(sfs[i]) && ((i > 1 && hide[i-1]) || (i < n && hide[i+1])) && (hide[i] = true)
    end
    hide[1] = false                                        # where the error was raised
    deleteat!(filtered, findall(hide))
    return filtered
end

function _install_frame_filter!()
    p = pathof(TraitWorld)
    _SRC_DIR[] = p === nothing ? "" : dirname(p) * "/"
    cb = Base.update_stackframes_callback[]
    cb === _hide_machinery_frames! && return nothing
    _PREV_FRAMES_CB[] = cb === identity ? nothing : cb
    Base.update_stackframes_callback[] = _hide_machinery_frames!
    return nothing
end

# ---------------------------------------------------------------------------
# A value that conforms to none of the traits bound at an argument reaches no method: Julia raises
# its `MethodError`, as plain Julia would ("identical or error"). The hint names the bound, so the
# message says what the argument should have been (note "Identical or error": errors name the bound).
# ---------------------------------------------------------------------------

function _bound_hint(io::IO, e::MethodError, @nospecialize(argtypes), @nospecialize(kwargs))
    f = e.f
    args = e.args
    args isa Tuple || return nothing
    n = length(args)
    for pos in 1:n
        Xs = try traits_at(f, pos, n) catch; Any[] end
        isempty(Xs) && continue
        a = args[pos]
        any(X -> try conforms(typeof(a), X) catch; false end, Xs) && continue
        print(io, "\nArgument ", pos, " of `", f, "` is bounded by ", join(string.(Xs), " or "),
              "; a ", typeof(a), " conforms to none of them (declare an implementation with `@implement`, or convert it).")
    end
    return nothing
end
_install_error_hints!() = (Base.Experimental.register_error_hint(_bound_hint, MethodError); nothing)
