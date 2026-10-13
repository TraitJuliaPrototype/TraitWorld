# ---------------------------------------------------------------------------
# Trait modules.
#
#     module Columns                       # in a package
#     using TraitWorld
#     @trait_module begin
#         …
#     end
#     end
#
#     @trait_module module Columns … end   # at the REPL or in a script
#
# Every top-level statement is wrapped in `@stmt`, so it is expanded only
# after the statements before it have run: traits and imports are known when
# a function definition is rewritten. `include` passes the same transform on.
#
# A function definition with trait-bounded arguments (`t::ColTable`,
# `t::(ColTable, RowTable)`, a bundle trait, `f::Callable{A, S}`) becomes
#   - a worker: the body as written, on `TObj{T} where {T >: Union{traits…}}`
#     and `CObj{A, S}`, compiled per representation; calls between workers
#     with matching bounds go straight to them (rule 3);
#   - an entry at `Any` in those positions, for ordinary callers: it projects
#     (rule 2), erases or passes functions, and calls the worker. An untyped
#     method of the same shape becomes the entry's fallback.
# ---------------------------------------------------------------------------

struct LayeringError <: Exception
    msg::String
end
Base.showerror(io::IO, e::LayeringError) = print(io, "LayeringError: ", e.msg)

struct OwnershipError <: Exception
    msg::String
end
Base.showerror(io::IO, e::OwnershipError) = print(io, "OwnershipError: ", e.msg)

"""
    is_trait_world(m::Module)

Base, Core, the standard libraries, TraitWorld itself, and every trait module
(and the modules inside one).
"""
function is_trait_world(m::Module)
    r = Base.moduleroot(m)
    (owner(r) === :Julia || r === TraitWorld) && return true
    x = m
    while true
        isdefined(x, :__trait_module__) && return true
        p = parentmodule(x)
        p === x && return false
        x = p
    end
end

macro trait_module(m)
    if m isa Expr && m.head === :module
        body = m.args[3]
        newbody = Expr(:block, _prologue()..., _transform_all(body.args)..., _epilogue())
        return esc(Expr(:module, m.args[1], m.args[2], newbody))
    end
    m isa Expr && m.head === :block || error("@trait_module: expected `module M … end` or a begin … end block")
    return esc(Expr(:toplevel, _prologue()..., _transform_all(m.args)..., _epilogue()))
end

_prologue() = Any[:(const __trait_module__ = true),
                  :(const __tw_entries__ = Dict{Any,Vector{Any}}()),
                  :(const __tw_plain__ = Dict{Any,Vector{Any}}()),
                  :(const __tw_checked__ = Set{Any}())]
_epilogue() = :($TraitWorld._finish_module(@__MODULE__))

function _transform_all(stmts)
    out = Any[]
    lnn = LineNumberNode(0, :none)
    for s in stmts
        if s isa LineNumberNode
            lnn = s
            push!(out, s)
        else
            push!(out, Expr(:macrocall, GlobalRef(TraitWorld, Symbol("@stmt")), lnn, s))
        end
    end
    return out
end
"The `include` transform: each top-level expression of an included file is a statement of the trait module."
_transform_file(ex) = Expr(:macrocall, GlobalRef(TraitWorld, Symbol("@stmt")), LineNumberNode(0, :none), ex)

macro stmt(ex)
    return esc(_process(__module__, ex))
end

const _PASS_MACROS = (Symbol("@inline"), Symbol("@noinline"))

function _process(mod::Module, ex)
    ex isa Expr || return ex
    h = ex.head
    if h === :toplevel || (h === :block && any(a -> !(a isa LineNumberNode), ex.args))
        return Expr(:toplevel, _transform_all(ex.args)...)
    elseif h === :using || h === :import
        return Expr(:toplevel, ex, :($TraitWorld._check_import(@__MODULE__, $(QuoteNode(ex)))))
    elseif h === :call && ex.args[1] === :include
        return Expr(:call, :include, GlobalRef(TraitWorld, :_transform_file), ex.args[2:end]...)
    elseif h === :module
        return Expr(:module, ex.args[1], ex.args[2],
                    Expr(:block, _prologue()..., _transform_all(ex.args[3].args)..., _epilogue()))
    elseif h === :macrocall
        name = ex.args[1]
        inner = ex.args[end]
        if (name in _PASS_MACROS || name == GlobalRef(Core, Symbol("@doc"))) && _is_fdef(inner)
            r = _rewrite_fdef(mod, inner)
            r === nothing && return ex
            # attach the macro (inline, or the docstring) to the worker
            worker, rest = r
            return Expr(:toplevel, Expr(:macrocall, ex.args[1:end-1]..., worker), rest...)
        end
        return ex
    elseif _is_fdef(ex)
        r = _rewrite_fdef(mod, ex)
        r === nothing && return ex
        worker, rest = r
        return Expr(:toplevel, worker, rest...)
    end
    return ex
end

function _is_fdef(ex)
    ex isa Expr || return false
    (ex.head === :function || ex.head === :(=)) || return false
    s = ex.args[1]
    while s isa Expr && s.head === :where
        s = s.args[1]
    end
    s isa Expr && s.head === :(::) && length(s.args) == 2 && (s = s.args[1])
    return s isa Expr && s.head === :call && (s.args[1] isa Symbol || (s.args[1] isa Expr && s.args[1].head === :.))
end

struct _Arg
    name::Any
    ann::Any        # the annotation as written, or nothing
    kind::Symbol    # :plain, :untyped, :trait, :callable, :vararg
    traits::Vector{Any}
    A::Any
    S::Any
    spec::Bool
end

function _classify(mod::Module, a)
    spec = false
    if a isa Expr && a.head === :macrocall && a.args[1] === Symbol("@specialize")
        spec = true
        a = a.args[end]
    end
    if a isa Symbol
        return _Arg(a, nothing, :untyped, Any[], nothing, nothing, spec)
    elseif a isa Expr && a.head === :...
        return _Arg(a, nothing, :vararg, Any[], nothing, nothing, false)
    elseif a isa Expr && a.head === :kw
        error("@trait_module: optional arguments are not supported in functions with trait-bounded arguments")
    elseif a isa Expr && a.head === :(::)
        name, ann = length(a.args) == 2 ? (a.args[1], a.args[2]) : (gensym(:arg), a.args[1])
        if ann isa Expr && ann.head === :tuple
            traits = Any[]
            for x in ann.args
                v = _tryeval(mod, x)
                is_trait(v) || error("@trait_module: `$x` in the bound `$ann` is not a trait")
                append!(traits, bound_traits(v))
            end
            return _Arg(name, ann, :trait, traits, nothing, nothing, spec)
        end
        v = _tryeval(mod, ann)
        if v isa Type && v !== Union{} && v <: Callable && v isa DataType
            A, S = v.parameters
            return _Arg(name, ann, :callable, Any[], A, S, spec)
        elseif is_trait(v)
            return _Arg(name, ann, :trait, bound_traits(v), nothing, nothing, spec)
        end
        return _Arg(name, ann, :plain, Any[], nothing, nothing, spec)
    end
    return _Arg(a, nothing, :plain, Any[], nothing, nothing, spec)
end

function _tryeval(mod::Module, ex)
    try
        return Core.eval(mod, ex)
    catch
        return nothing
    end
end

_uses(ex, s::Symbol) = ex === s || (ex isa Expr && any(a -> _uses(a, s), ex.args))
_wherevar(w) = w isa Symbol ? w : (w isa Expr && w.head in (:<:, :>:) ? w.args[1] : w)

"The key under which a function's entries are recorded: (owning module, name)."
function _fkey(mod::Module, fname)
    if fname isa Symbol
        if isdefined(mod, fname)
            f = getfield(mod, fname)
            f isa Function && return (parentmodule(f), nameof(f))
        end
        return (mod, fname)
    end
    f = Core.eval(mod, fname)
    return (parentmodule(f), nameof(f))
end
function _registry(mod::Module, key, which::Symbol)
    owner_mod = key[1]
    regmod = isdefined(owner_mod, which) ? owner_mod : mod
    isdefined(regmod, which) || return nothing
    return getfield(regmod, which)::Dict{Any,Vector{Any}}
end

function _rewrite_fdef(mod::Module, ex)
    head = ex.head
    sig, body = ex.args[1], ex.args[2]
    wheres = Any[]
    while sig isa Expr && sig.head === :where
        wheres = Any[sig.args[2:end]..., wheres...]
        sig = sig.args[1]
    end
    ret = nothing
    if sig isa Expr && sig.head === :(::)
        ret = sig.args[2]
        sig = sig.args[1]
    end
    fname = sig.args[1]
    rawargs = sig.args[2:end]
    if any(a -> a isa Expr && a.head === :parameters, rawargs)
        return nothing      # keyword arguments: plain Julia (trait-bounded ones are rejected below)
    end
    args = [_classify(mod, a) for a in rawargs]
    key = _fkey(mod, fname)
    pattern = Any[(x.kind in (:trait, :callable, :untyped)) ? nothing : x.ann for x in args]
    entries = _registry(mod, key, :__tw_entries__)
    plain = _registry(mod, key, :__tw_plain__)
    istraitdef = any(x -> x.kind in (:trait, :callable), args)
    if !istraitdef
        # an untyped method shaped like an existing entry is that entry's fallback
        if entries !== nothing && pattern in get(entries, key, Any[])
            newcall = Expr(:call, fname, :(::$TraitWorld.Untyped), rawargs...)
            s = ret === nothing ? newcall : Expr(:(::), newcall, ret)
            for w in wheres
                s = Expr(:where, s, w)
            end
            return Expr(head, s, body), Any[:($TraitWorld._check_methods(@__MODULE__, $(QuoteNode(fname))))]
        end
        plain === nothing || push!(get!(plain, key, Any[]), pattern)
        return ex, Any[:($TraitWorld._check_methods(@__MODULE__, $(QuoteNode(fname))))]
    end
    any(x -> x.kind === :vararg, args) && error("@trait_module: varargs are not supported in `$fname` with trait-bounded arguments")
    # --- the worker
    wargs = Any[]
    newwheres = Any[]
    for x in args
        if x.kind === :trait
            T = gensym(:T)
            closure = Any[]
            for X in x.traits, Y in trait_closure(X)
                any(z -> z === Y, closure) || push!(closure, Y)
            end
            push!(newwheres, Expr(:(>:), T, Expr(:curly, :Union, closure...)))
            push!(wargs, :($(x.name)::$TraitWorld.TObj{$T}))
        elseif x.kind === :callable
            push!(wargs, :($(x.name)::$TraitWorld.CObj{$(x.A),$(x.S)}))
        elseif x.kind === :untyped
            push!(wargs, x.name)
        else
            push!(wargs, x.ann === nothing ? x.name : :($(x.name)::$(x.ann)))
        end
    end
    wsig = Expr(:call, fname, wargs...)
    ret === nothing || (wsig = Expr(:(::), wsig, ret))
    allwheres = Any[wheres..., newwheres...]
    isempty(allwheres) || (wsig = Expr(:where, wsig, allwheres...))
    worker = Expr(head, wsig, _rethrow_piracy(body))
    rest = Any[]
    # --- the entry, once per shape
    existing = entries === nothing ? Any[] : get(entries, key, Any[])
    if !(pattern in existing)
        if plain !== nothing && pattern in get(plain, key, Any[])
            error("@trait_module: `$fname` already has an untyped method of the shape its trait-bounded method needs " *
                  "for an entry; define the trait-bounded methods first, then the untyped fallback")
        end
        if key[1] !== mod
            # an entry is a method at Any: only the function's owner may add one (rule 5)
            owner(key[1]) === owner(mod) || error("@trait_module: `$fname` belongs to $(key[1]); $(mod) may add trait-bounded " *
                                                  "methods to it only where it already has an entry of that shape (rule 5)")
        end
        nargs = length(args)
        eargs = Any[]
        stmts = Any[]
        callnames = Any[]
        for (i, x) in enumerate(args)
            nm = x.name
            push!(callnames, nm)
            if x.kind === :trait
                push!(eargs, :(@nospecialize($nm)))
            elseif x.kind === :callable
                push!(eargs, :(@nospecialize($nm)))
            elseif x.kind === :untyped
                push!(eargs, nm)
            else
                push!(eargs, x.ann === nothing ? nm : :($nm::$(x.ann)))
            end
        end
        newnames = Any[]
        for (i, x) in enumerate(args)
            if x.kind === :trait
                v = gensym(Symbol(x.name, :_view))
                cache = gensym(Symbol(x.name, :_cache))
                push!(rest, :(const $cache = $TraitWorld.EntryCache()))
                push!(stmts, :($v = $TraitWorld.enter($cache, $fname, $i, $nargs, $(x.name))))
                push!(stmts, :($v === $TraitWorld.NOTRAIT && return $TraitWorld.fallback($fname, $(callnames...))))
                push!(newnames, v)
            elseif x.kind === :callable
                v = gensym(Symbol(x.name, :_fn))
                push!(stmts, :($v = $TraitWorld.enter_callable($(x.A), $(x.S), $(x.spec), $(x.name))))
                push!(newnames, v)
            else
                push!(newnames, x.name)
            end
        end
        push!(stmts, :(return $TraitWorld.checked_call($fname, $(newnames...))))
        kept = Any[w for w in wheres if any(x -> x.kind === :plain && x.ann !== nothing && _uses(x.ann, _wherevar(w)), args)]
        esig = Expr(:call, fname, eargs...)
        isempty(kept) || (esig = Expr(:where, esig, kept...))
        push!(rest, Expr(:function, esig, Expr(:block, stmts...)))
        if entries !== nothing
            push!(get!(entries, key, Any[]), pattern)
        end
    end
    push!(rest, :($TraitWorld._check_methods(@__MODULE__, $(QuoteNode(fname)))))
    return worker, rest
end

"""
Inside trait-bound code, `catch` must not swallow a `PiracyError`: a fallback
taken after it would compute something plain Julia never computes.
"""
function _rethrow_piracy(ex)
    ex isa Expr || return ex
    args = Any[_rethrow_piracy(a) for a in ex.args]
    if ex.head === :try && length(args) >= 3 && args[3] isa Expr
        var = args[2]
        if var === false
            var = gensym(:err)
            args[2] = var
        end
        args[3] = Expr(:block, :($var isa $TraitWorld.PiracyError && rethrow()), args[3])
    end
    return Expr(ex.head, args...)
end

# --- checks ----------------------------------------------------------------------

function _module_path(mod::Module, path::Expr)
    syms = Symbol[a for a in path.args]
    i = 1
    m = mod
    if syms[1] === :.
        while i <= length(syms) && syms[i] === :.
            i += 1
        end
        for _ in 1:(i-2)
            m = parentmodule(m)
        end
    else
        name = syms[1]
        if isdefined(mod, name) && getfield(mod, name) isa Module
            m = getfield(mod, name)
        else
            m = _loaded_module(name)
        end
        i = 2
    end
    while i <= length(syms)
        isdefined(m, syms[i]) || break
        x = getfield(m, syms[i])
        x isa Module || break
        m = x
        i += 1
    end
    return m
end
function _loaded_module(name::Symbol)
    for (k, v) in Base.loaded_modules
        k.name == String(name) && return v
    end
    error("@trait_module: cannot find the module `$name`")
end

"Rule 1, at the import: a trait module imports only the trait world."
function _check_import(mod::Module, ex::Expr)
    paths = Expr[]
    for a in ex.args
        if a isa Expr && a.head === :(:)
            push!(paths, a.args[1])
        elseif a isa Expr && a.head === :.
            push!(paths, a)
        elseif a isa Expr && a.head === :as
            push!(paths, a.args[1])
        end
    end
    for p in paths
        target = _module_path(mod, p)
        is_trait_world(target) || throw(LayeringError(
            "trait module $mod imports $target, which is outside the trait world. Layering (rule 1): ordinary code may " *
            "use the trait world, the trait world uses only itself. Make $target a trait module, or call it from an " *
            "ordinary module that uses both."))
    end
    return nothing
end

"Rule 5: every method a trait module defines is owned by its package, in every signature it applies to."
function _check_methods(mod::Module, fname)
    f = Core.eval(mod, fname)
    for m in methods(f)
        m.module === mod || continue
        owned_method(m) && continue
        throw(OwnershipError("$(m) is defined by $(mod), which owns neither its function nor its types " *
                             "in every signature it applies to (rule 5)"))
    end
    return nothing
end

"""
At the end of a trait module: every pair of workers whose bounds at a
position are unrelated needs a worker with both bounds (resolving method).
"""
function _finish_module(mod::Module)
    # imports made outside the checked statements (before the block) count too
    for u in ccall(:jl_module_usings, Any, (Any,), mod)::Vector{Any}
        u isa Module || continue
        is_trait_world(u) || throw(LayeringError(
            "trait module $mod uses $u, which is outside the trait world (rule 1)"))
    end
    isdefined(mod, :__tw_entries__) || return nothing
    for key in keys(mod.__tw_entries__)
        key[1] === mod || continue
        isdefined(mod, key[2]) || continue
        check_bounds(getfield(mod, key[2]))
    end
    return nothing
end

"The unresolved pairs of bounds of `f`'s workers; throws if there are any."
function check_bounds(@nospecialize(f))
    ws = Any[]
    for m in methods(f)
        sig = Base.unwrap_unionall(m.sig)
        bs = Any[]
        rest = Any[]
        any_t = false
        for p in sig.parameters[2:end]
            lb = _tobj_lb(p)
            if lb === nothing
                push!(bs, nothing)
                push!(rest, p)
            else
                any_t = true
                push!(bs, Base.uniontypes(lb))
                push!(rest, :trait)
            end
        end
        any_t && push!(ws, (m, bs, rest))
    end
    implies(a, b) = all(x -> any(y -> y === x, a), b)       # a carries every trait of b
    problems = String[]
    for i in 1:length(ws), j in i+1:length(ws)
        (m1, b1, r1), (m2, b2, r2) = ws[i], ws[j]
        length(b1) == length(b2) || continue
        all(k -> (b1[k] === nothing) == (b2[k] === nothing), 1:length(b1)) || continue
        isequal(r1, r2) || continue
        all(k -> b1[k] === nothing || implies(b1[k], b2[k]), 1:length(b1)) && continue
        all(k -> b1[k] === nothing || implies(b2[k], b1[k]), 1:length(b1)) && continue
        resolved = any(ws) do (m3, b3, r3)
            length(b3) == length(b1) && isequal(r3, r1) &&
                all(k -> b1[k] === nothing || (implies(b3[k], b1[k]) && implies(b3[k], b2[k])), 1:length(b1))
        end
        resolved || push!(problems, "$(m1) and $(m2) have unrelated bounds, and no method has both")
    end
    isempty(problems) || throw(TraitBoundError("ambiguous trait-bounded methods of `$f`:\n  " * join(problems, "\n  ") *
                                               "\nAdd a method with both bounds, as in f(t::(A, B))."))
    return nothing
end
