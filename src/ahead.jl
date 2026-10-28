# ---------------------------------------------------------------------------
# Compiling ahead from declared implementations (plan step 4, design §4.8).
#
# While a package that declares `@implement X T` is precompiled, the code that calls with a `T`
# need is compiled into that package's image: for every entry position whose bound includes `X`,
#   - the worker at the trait object of `T`'s builder, where its other arguments are declared
#     concrete (typed callers inline the entry and call it);
#   - the entry's method specialized on the builder (untyped.jl), for `Compiled` values whose
#     callers do not know the type (`compiled_for`): compiled once per key.
# The list is exact, because implementations are declared: Rust compiles a generic function in the
# crate that sees both it and the type; Swift's cross-module specialization and C++'s explicit
# instantiation do the same. The images keep code compiled for other modules' functions (piece 5).
# ---------------------------------------------------------------------------

"Compile ahead for a declared implementation in module `mod`, while its package is built; nothing in a session."
function _compile_ahead(mod::Module, @nospecialize(X), @nospecialize(T))
    ccall(:jl_generating_output, Cint, ()) == 1 || return nothing
    get(ENV, "JULIA_TW_AHEAD", "1") == "0" && return nothing
    _latest(_compile_ahead_now, mod, X, T)
    return nothing
end

# --- A check's record kept with the code it checked (the facts-first review §2.4) -----------------------
# A first-call check that passes while a package image is built is recorded in a module of that image, as
# `(sig, the worker methods it checked)` in `__tw_checked__`. A first call looks it up in the few modules
# the signature names, not in every module after every load; the record holds while dispatch selects
# the same worker methods, so a redefined worker is checked again.

"The worker methods dispatch selects at `sig` (its methods that are not entries): what a check's record is valid for."
function _worker_methods(@nospecialize(sig))
    ms = Base._methods_by_ftype(_worker_sig(sig), -1, Base.get_world_counter())
    ms isa Vector || return Method[]
    return Method[(m::Core.MethodMatch).method for m in ms if !_is_entry((m::Core.MethodMatch).method)]
end
"The modules a signature names, where its check's record may live: its function's, then its types'."
function _record_modules(@nospecialize(sig))
    out = Module[]
    walk(@nospecialize(x), depth) = depth > 3 ? nothing :
        x isa DataType ? (push!(out, parentmodule(x)); foreach(p -> walk(p, depth + 1), x.parameters)) :
        x isa Union ? (walk(x.a, depth); walk(x.b, depth)) : x isa UnionAll ? walk(Base.unwrap_unionall(x), depth) : nothing
    walk(_worker_ftype(sig), 0)
    foreach(p -> walk(p, 1), _worker_sig(sig).parameters)
    return unique!(out)
end
"Whether an image holds a record that `sig`'s check passed for the worker methods dispatch selects now."
function _recorded_check(@nospecialize(sig))
    ws = nothing
    for m in _record_modules(sig)
        # defined by `eval` while the image was built, perhaps after this world: read in the latest
        Base.invokelatest(isdefined, m, :__tw_checked__) || continue
        for e in Base.invokelatest(getglobal, m, :__tw_checked__)
            e isa Tuple{Any,Vector{Method}} && e[1] == sig || continue
            ws === nothing && (ws = _worker_methods(sig))
            e[2] == ws && return true
        end
    end
    return false
end
"Record that `sig`'s check passed, in the first of `mods` that belongs to the image being built."
function _record_check!(@nospecialize(sig), mods)
    rec = (sig, _worker_methods(sig))
    for m in mods
        # bindings defined by `eval` here are read in the latest world
        if !Base.invokelatest(isdefined, m, :__tw_checked__)
            try
                Core.eval(m, :(const __tw_checked__ = Any[]))
            catch
                continue                               # a closed module: another image's
            end
        end
        push!(Base.invokelatest(getglobal, m, :__tw_checked__), rec)
        return true
    end
    return false                                       # no open module: checked at the first call
end
"""
Run the first-call check of a worker signature now, and keep it with the image being built: in the
module of the implementing type `T`, else the module the declaration was expanded in (an
implementation with operations is expanded in its trait's module, which belongs to another image).
"""
function _check_ahead!(mod::Module, @nospecialize(T), @nospecialize(sig))
    _check_once(Ref(false), sig)                       # throws as a first call would: the build fails; records it
    _recorded_check(sig) || _record_check!(sig, (T isa DataType ? parentmodule(T) : mod, mod))
    return nothing
end

"The trait modules loaded now: modules (and their submodules) made by `@trait_module`."
function _trait_modules()
    out = Module[]
    seen = Base.IdSet{Module}()
    todo = Module[m for m in values(Base.loaded_modules)]
    while !isempty(todo)
        m = pop!(todo)
        m in seen && continue
        push!(seen, m)
        isdefined(m, :__trait_module__) && isdefined(m, :__tw_positions__) && push!(out, m)
        for n in names(m; all = true, imported = false)
            isdefined(m, n) || continue
            v = getglobal(m, n)
            v isa Module && v !== m && parentmodule(v) === m && push!(todo, v)
        end
    end
    return out
end

@machinery function _compile_ahead_now(mod::Module, @nospecialize(X), @nospecialize(T))
    (T isa DataType && isconcretetype(T)) || return nothing
    FX = _family(X)
    n = 0
    for mod in _trait_modules()
        for (f, pos, nargs) in mod.__tw_positions__
            nargs < 0 && continue
            L = needed(EntryPos{typeof(f),pos,nargs}())
            Xs = Any[typeof(L).parameters[1].parameters...]
            any(Y -> _family(Y) === FX, Xs) || continue
            b = _builder_for(Xs, T)
            b isa Builder || continue
            V = Base.infer_return_type(b, (T,))
            (V isa DataType && V <: TObj) || continue
            # the workers whose only trait position is `pos`, other arguments concrete
            for m in methods(f)
                _isworker(m) || continue
                ps = Base.unwrap_unionall(m.sig).parameters
                length(ps) - 1 == nargs || continue
                argt = Any[]
                for i in 1:nargs
                    p = ps[i + 1]
                    if i == pos
                        push!(argt, V)                  # checked against the whole signature below
                    elseif isconcretetype(p) && _tobj_lb(p) === nothing
                        push!(argt, p)
                    else
                        empty!(argt); break
                    end
                end
                if length(argt) == nargs && Tuple{typeof(f),argt...} <: m.sig && precompile(f, Tuple(argt))
                    n += 1
                    _check_ahead!(mod, T, Tuple{typeof(f),argt...})
                end
            end
            # the entry's method for `Compiled` values whose callers do not know the type: once per builder (key)
            for (g, gn, tag, tpos) in mod.__tw_untyped__
                (g === f && gn == nargs && tpos == (pos,)) || continue
                for cm in methods(tag)
                    cps = Any[Base.unwrap_unionall(cm.sig).parameters...]
                    length(cps) == 2 + nargs || continue
                    cps[2] = typeof(b)
                    all(isconcretetype, (cps[i] for i in 3:length(cps) if i - 2 != pos)) || continue
                    precompile(Tuple{cps...}) && (n += 1)
                end
            end
        end
    end
    _FACTS_DEBUG[] && Core.println("TraitWorld: compiled ahead for ", X, " ", T, ": ", n, " signatures")
    return nothing
end
