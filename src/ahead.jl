# ---------------------------------------------------------------------------
# Compiling ahead from declared implementations (plan step 4, design §4.8).
#
# While a package that declares `@implement X T` is precompiled, the code that calls with a `T`
# need is compiled into that package's image: for every entry position whose bound includes `X`,
#   - the worker at the trait object of `T`'s builder, where its other arguments are declared
#     concrete (typed callers inline the entry and call it);
#   - the entry's method specialized on the builder (untyped.jl), for callers that do not know
#     the type: compiled once per key;
#   - the entry for `T` itself, for shapes the table does not serve yet (specialized entries).
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

"""
Worker signatures whose first-call check (`_check_once`) passed while a package image was built:
each declaring module keeps its own in `__tw_checked__`, saved in its image, and a load adds them here.
"""
const _CHECKED_AHEAD = Ref(Base.IdSet{Any}())          # copy-on-write
"After a package load: the checks its image holds."
function _note_checked_ahead!(root::Module)
    found = Any[]
    seen = Base.IdSet{Module}()
    todo = Module[root]
    while !isempty(todo)
        m = pop!(todo)
        m in seen && continue
        push!(seen, m)
        isdefined(m, :__tw_checked__) && append!(found, getglobal(m, :__tw_checked__))
        for n in names(m; all = true, imported = false)
            isdefined(m, n) || continue
            v = getglobal(m, n)
            v isa Module && v !== m && parentmodule(v) === m && push!(todo, v)
        end
    end
    isempty(found) && return nothing
    @lock _LOCK begin
        s = copy(_CHECKED_AHEAD[])
        foreach(x -> push!(s, x), found)
        _CHECKED_AHEAD[] = s
    end
    return nothing
end
"""
Run the first-call check of a worker signature now, and keep it with the image being built: in the
module of the implementing type `T`, else the module the declaration was expanded in (an
implementation with operations is expanded in its trait's module, which belongs to another image).
"""
function _check_ahead!(mod::Module, @nospecialize(T), @nospecialize(sig))
    _check_once(Ref(false), sig)                       # throws as a first call would: the build fails
    for m in (T isa DataType ? parentmodule(T) : mod, mod)
        if !isdefined(m, :__tw_checked__)
            try
                Core.eval(m, :(const __tw_checked__ = Any[]))
            catch
                continue                               # a closed module: another image's
            end
        end
        push!(getglobal(m, :__tw_checked__), sig)
        return nothing
    end
    return nothing                                     # no open module: checked at the first call
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
            # the entry's method for callers that do not know the type: once per builder (key)
            tabled = false
            for (g, gn, tag, tpos) in mod.__tw_untyped__
                (g === f && gn == nargs && tpos == (pos,)) || continue
                tabled = true
                for cm in methods(tag)
                    cps = Any[Base.unwrap_unionall(cm.sig).parameters...]
                    length(cps) == 2 + nargs || continue
                    cps[2] = typeof(b)
                    all(isconcretetype, (cps[i] for i in 3:length(cps) if i - 2 != pos)) || continue
                    precompile(Tuple{cps...}) && (n += 1)
                end
                # and an entry method for `T` itself, in this package: a caller that does not know the
                # type reaches it by one dispatch, as plain Julia's code for a type
                n += _ahead_entry!(mod, T, f, pos, nargs)
            end
            # an entry not served by the table: the entry for `T` itself
            if !tabled
                for m in methods(f)
                    _is_entry(m) || continue
                    ps = Base.unwrap_unionall(m.sig).parameters
                    length(ps) - 1 == nargs || continue
                    argt = Any[i == pos ? T : ps[i + 1] for i in 1:nargs]
                    all(isconcretetype, argt) && precompile(f, Tuple(argt)) && (n += 1)
                end
            end
        end
    end
    _FACTS_DEBUG[] && Core.println("TraitWorld: compiled ahead for ", X, " ", T, ": ", n, " signatures")
    return nothing
end

"""
The entry method for type `T` at position `pos` of `f`'s tabled entry, defined in this package (the
module of `T`, else the declaring module) and compiled into its image: `f(x::T, …)` invokes the
generic entry at `T`, so it is the generic entry's folded path. Dispatch picks it for a `T`, and
the generic entry (the table, untyped.jl) for every type not compiled ahead. The package owns
`T`: a stakeholder's method, no pirate. Returns the number of signatures compiled.
"""
function _ahead_entry!(mod::Module, @nospecialize(T), @nospecialize(f), pos::Int, nargs::Int)
    (f isa Function && isdefined(parentmodule(f), nameof(f)) && getglobal(parentmodule(f), nameof(f)) === f) || return 0
    for m in methods(f)
        _is_entry(m) || continue
        m.sig isa DataType || continue                      # a `where` entry: not specialized ahead
        ps = m.sig.parameters
        length(ps) - 1 == nargs && ps[pos + 1] === Any || continue
        argt = Any[i == pos ? T : ps[i + 1] for i in 1:nargs]
        all(isconcretetype, argt) || continue
        Base.hasmethod(f, Tuple{argt...}) && which(f, Tuple{argt...}) !== m && return 0   # defined already
        as = [Symbol(:a, i) for i in 1:nargs]
        name = Expr(:., parentmodule(f), QuoteNode(nameof(f)))
        def = Expr(:macrocall, GlobalRef(Base, Symbol("@inline")), LineNumberNode(0, :none),
                   Expr(:function, Expr(:call, name, [:($(as[i])::$(argt[i])) for i in 1:nargs]...),
                        Expr(:block, Expr(:meta, :facts, 0), :(return invoke($f, $(Tuple{ps[2:end]...}), $(as...))))))
        for dm in (T isa DataType ? parentmodule(T) : mod, mod)
            try
                isdefined(dm, :__tw_ahead_entries__) || Core.eval(dm, :(const __tw_ahead_entries__ = true))
                Core.eval(dm, def)
            catch
                continue                                     # a closed module: another image's
            end
            return precompile(f, Tuple(argt)) ? 1 : 0
        end
        return 0
    end
    return 0
end
