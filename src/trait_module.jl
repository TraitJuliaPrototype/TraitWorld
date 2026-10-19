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
#     with matching bounds go straight to them (rule 2);
#   - an entry at `Any` in those positions, for ordinary callers: it projects
#     (rule 2), erases or passes functions, and calls the worker. An untyped
#     method of the same shape becomes the entry's fallback.
# ---------------------------------------------------------------------------

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

_prologue() = Any[:(Base.Experimental.@compiler_options facts=true),     # Julia compiles the module by facts
                  :(const __trait_module__ = true),
                  :(const __tw_entries__ = Dict{Any,Vector{Any}}()),
                  :(const __tw_plain__ = Dict{Any,Vector{Any}}()),
                  :(const __tw_extended__ = Set{Any}()),          # other modules' functions given workers here
                  :(const __tw_methods_seen__ = Base.IdSet{Method}()),
                  :(const __tw_positions__ = Any[]),          # (function, position, nargs) of the entries' trait positions
                  :(const __tw_finished__ = Ref(false))]
_epilogue() = :($TraitWorld._latest($TraitWorld._finish_module, @__MODULE__))

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
        return ex                                   # a trait module may use any Julia code
    elseif h === :call && ex.args[1] === :include
        return Expr(:call, :include, GlobalRef(TraitWorld, :_transform_file), ex.args[2:end]...)
    elseif h === :module
        return Expr(:module, ex.args[1], ex.args[2],
                    Expr(:block, _prologue()..., _transform_all(ex.args[3].args)..., _epilogue()))
    elseif h === :macrocall && _concrete_macro_level(ex.args[1]) !== nothing && _is_fdef(ex.args[end])
        # @warn_on_abstract / @error_on_abstract on one function
        level = _concrete_macro_level(ex.args[1])
        inner = ex.args[end]
        fname = _fdef_name(inner)
        r = _process(mod, inner)
        return Expr(:toplevel, r, :($TraitWorld.concrete_level(::typeof($fname)) = $(QuoteNode(level))))
    elseif h === :struct
        return _dynamic_fields(mod, ex)
    elseif h === :macrocall
        name = ex.args[1]
        inner = ex.args[end]
        if name == GlobalRef(Core, Symbol("@doc")) && inner isa Expr && inner.head === :struct
            return Expr(:macrocall, ex.args[1:end-1]..., _dynamic_fields(mod, inner))
        end
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

"""
A trait's name in a struct field or a container means its dynamic value, as an
abstract type's name there means a boxed value (note "Traits as abstract
types"): `plots::Vector{Plot}` is `Vector{Dynamic{Plot}}`, `bg::ColorSpec` is
`Dynamic{ColorSpec}`. `Vector{<:ColTable}` keeps its meaning, one representation.
"""
function _dynamic_fields(mod::Module, ex::Expr)
    body = ex.args[3]
    body isa Expr && body.head === :block || return ex
    newbody = Any[]
    for f in body.args
        if f isa Expr && f.head === :(::) && length(f.args) == 2
            push!(newbody, Expr(:(::), f.args[1], _dyn_type(mod, f.args[2])))
        elseif f isa Expr && f.head === :const && f.args[1] isa Expr && f.args[1].head === :(::)
            g = f.args[1]
            push!(newbody, Expr(:const, Expr(:(::), g.args[1], _dyn_type(mod, g.args[2]))))
        else
            push!(newbody, f)
        end
    end
    return Expr(:struct, ex.args[1], ex.args[2], Expr(:block, newbody...))
end

function _dyn_type(mod::Module, T)
    T isa Expr && T.head === :curly && _tryeval(mod, T.args[1]) === Dynamic && return T
    if T isa Symbol || (T isa Expr && T.head === :.)
        v = _tryeval(mod, T)
        return (v isa Type && is_trait(v)) ? :($TraitWorld.Dynamic{$T}) : T
    elseif T isa Expr && T.head === :curly
        h = _tryeval(mod, T.args[1])
        h isa Type && is_trait(h) && return :($TraitWorld.Dynamic{$T})
        return Expr(:curly, T.args[1], Any[(a isa Expr && a.head === :(<:)) ? a : _dyn_type(mod, a) for a in T.args[2:end]]...)
    end
    return T
end

"""
A trait's name as a container's element type in a function means its dynamic value, as in a
field (note "Traits as abstract types"): `Column[]`, `Column[a, b]`, `Vector{Column}(undef, n)`
and `Dict{String, Column}()` in a body; `cs::Vector{Column}` in an argument. A trait's name in
an argument itself stays a bound, and `Vector{<:ColTable}` keeps its meaning.
"""
function _dynamic_containers(mod::Module, ex::Expr)
    sig, body = ex.args[1], ex.args[2]
    return Expr(ex.head, _dyn_sig(mod, sig), _dyn_body(mod, body))
end
_istraitname(mod::Module, x) = (x isa Symbol || (x isa Expr && x.head === :.)) && (v = _tryeval(mod, x); v isa Type && is_trait(v))
function _dyn_sig(mod::Module, s)
    s isa Expr || return s
    if s.head === :where
        return Expr(:where, _dyn_sig(mod, s.args[1]), s.args[2:end]...)
    elseif s.head === :call
        return Expr(:call, s.args[1], Any[_dyn_arg(mod, a) for a in s.args[2:end]]...)
    elseif s.head === :(::) && length(s.args) == 2 && s.args[1] isa Expr && s.args[1].head === :call
        return Expr(:(::), _dyn_sig(mod, s.args[1]), s.args[2])
    end
    return s
end
function _dyn_arg(mod::Module, a)
    a isa Expr || return a
    if a.head === :parameters || a.head === :kw || a.head === :...
        return Expr(a.head, Any[_dyn_arg(mod, x) for x in a.args]...)
    elseif a.head === :(::) && length(a.args) == 2 && a.args[2] isa Expr && a.args[2].head === :curly && !_istraitname(mod, a.args[2].args[1])
        return Expr(:(::), a.args[1], _dyn_type(mod, a.args[2]))
    end
    return a
end
function _dyn_body(mod::Module, x)
    x isa Expr || return x
    x.head in (:quote, :inert, :meta) && return x
    if x.head in (:ref, :typed_vcat, :typed_hcat, :typed_comprehension) && _istraitname(mod, x.args[1])
        return Expr(x.head, :($TraitWorld.Dynamic{$(x.args[1])}), Any[_dyn_body(mod, a) for a in x.args[2:end]]...)
    elseif x.head === :curly && !_istraitname(mod, x.args[1]) && any(a -> _istraitname(mod, a), x.args[2:end])
        return _dyn_type(mod, x)
    end
    return Expr(x.head, Any[_dyn_body(mod, a) for a in x.args]...)
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

function _fdef_name(ex)
    s = ex.args[1]
    while s isa Expr && s.head === :where
        s = s.args[1]
    end
    s isa Expr && s.head === :(::) && (s = s.args[1])
    return s.args[1]
end

struct _Arg
    name::Any
    ann::Any        # the annotation as written, or nothing
    kind::Symbol    # :plain, :untyped, :trait, :callable, :callables, :vararg, :vararg_trait
    traits::Vector{Any}
    A::Any
    S::Any
    M::Any          # the Callable mode the bound names, or nothing (either mode, the default supplied)
    default::Any    # a keyword's default, or nothing
    required::Bool  # a keyword without a default
end
_Arg(name, ann, kind, traits, A, S, M) = _Arg(name, ann, kind, traits, A, S, M, nothing, false)

"The parameters of a `Callable` bound: `(A, S, M)`, with `M === nothing` when the bound leaves the mode open."
function _callable_params(@nospecialize(v))
    v isa Type && v !== Union{} && v <: Callable || return nothing
    u = Base.unwrap_unionall(v)
    u isa DataType && u.name === Base.typename(Callable) || return nothing
    A, S, M = u.parameters
    (A isa TypeVar || S isa TypeVar) && return nothing
    return (A, S, M isa TypeVar ? nothing : M)
end

function _classify(mod::Module, a, unbounded::Vector{Symbol} = Symbol[])
    if a isa Expr && a.head === :macrocall && a.args[1] === Symbol("@specialize")
        error("@trait_module: `@specialize` is retired; write the mode in the bound, `f::Callable{A, S, CompiledCall}`, " *
              "or let the caller choose with `compiled_call(f)`")
    end
    if a isa Symbol
        return _Arg(a, nothing, :untyped, Any[], nothing, nothing, nothing)
    elseif a isa Expr && a.head === :...
        inner = _classify(mod, a.args[1], unbounded)
        inner.kind === :trait && return _Arg(inner.name, inner.ann, :vararg_trait, inner.traits, nothing, nothing, nothing)
        inner.kind in (:callable, :callables) && error("@trait_module: a vararg of `Callable` is not supported")
        return _Arg(a, nothing, :vararg, Any[], nothing, nothing, nothing)
    elseif a isa Expr && a.head === :kw
        x = _classify(mod, a.args[1], unbounded)
        return _Arg(x.name, x.ann, x.kind, x.traits, x.A, x.S, x.M, a.args[2], false)
    elseif a isa Expr && a.head === :(::)
        name, ann = length(a.args) == 2 ? (a.args[1], a.args[2]) : (gensym(:arg), a.args[1])
        # `x::T where T` with no bound is untyped: it must not take the entry's place
        ann isa Symbol && ann in unbounded && return _Arg(name, ann, :untyped, Any[], nothing, nothing, nothing)
        if ann isa Expr && ann.head === :tuple
            vs = Any[_tryeval(mod, x) for x in ann.args]
            cps = Any[_callable_params(v) for v in vs]
            if all(c -> c !== nothing, cps)
                # several Callable bounds: the function is called at each signature
                return _Arg(name, ann, :callables, cps, nothing, nothing, nothing)
            end
            traits = Any[]
            for (x, v) in zip(ann.args, vs)
                is_trait(v) || error("@trait_module: `$x` in the bound `$ann` is not a trait")
                append!(traits, bound_traits(v))
            end
            return _Arg(name, ann, :trait, traits, nothing, nothing, nothing)
        end
        v = _tryeval(mod, ann)
        cp = _callable_params(v)
        if cp !== nothing
            return _Arg(name, ann, :callable, Any[], cp[1], cp[2], cp[3])
        elseif is_trait(v)
            return _Arg(name, ann, :trait, bound_traits(v), nothing, nothing, nothing)
        end
        return _Arg(name, ann, :plain, Any[], nothing, nothing, nothing)
    end
    return _Arg(a, nothing, :plain, Any[], nothing, nothing, nothing)
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

"A keyword parameter of a trait-bounded function, classified like a positional one."
function _classify_kw(mod::Module, p, unbounded::Vector{Symbol})
    if p isa Expr && p.head === :...
        return _Arg(p.args[1], nothing, :kwrest, Any[], nothing, nothing, nothing)
    end
    x = _classify(mod, p, unbounded)
    required = !(p isa Expr && p.head === :kw)
    x.kind === :untyped && (x = _Arg(x.name, nothing, :plain, Any[], nothing, nothing, nothing, x.default, required))
    x.kind in (:vararg, :vararg_trait, :callables) && error("@trait_module: unsupported keyword parameter `$p`")
    return _Arg(x.name, x.ann, x.kind, x.traits, x.A, x.S, x.M, x.default, required)
end

"Reassemble a signature: `f(args...; kws...)::ret where {wheres...}`."
function _mksig(fname, args, kws, ret, wheres)
    s = isempty(kws) ? Expr(:call, fname, args...) : Expr(:call, fname, Expr(:parameters, kws...), args...)
    ret === nothing || (s = Expr(:(::), s, ret))
    # one `where {…}`: a type variable declared earlier is in scope in a later bound (`R1, T >: ColTable{R1}`)
    isempty(wheres) || (s = Expr(:where, s, wheres...))
    return s
end

"""
Positional defaults are what Julia makes of them: the full method, and one
shorter method per default whose body calls the full one. Each is then a
trait-bounded definition of its own, with its own entry (rule 2: the shorter
method passes its own trait object on).
"""
function _expand_defaults(mod::Module, head, fname, rawargs, kwparams, wheres, ret, body)
    names = Any[]
    full = Any[]
    for a in rawargs
        if a isa Expr && a.head === :kw
            push!(full, a.args[1])
        else
            push!(full, a)
        end
        x = a isa Expr && a.head === :kw ? a.args[1] : a
        x isa Expr && x.head === :(::) && (x = length(x.args) == 2 ? x.args[1] : gensym(:arg))
        x isa Expr && x.head === :... && (x = x.args[1] isa Expr ? x.args[1].args[1] : x.args[1])
        push!(names, x)
    end
    firstdef = findfirst(a -> a isa Expr && a.head === :kw, rawargs)
    defs = Any[Expr(head, _mksig(fname, full, kwparams, ret, wheres), body)]
    kwforward = isempty(kwparams) ? Any[] : Any[Expr(:parameters, Expr(:..., :kws))]
    kwtake = isempty(kwparams) ? Any[] : Any[Expr(:..., :kws)]
    for k in length(rawargs):-1:firstdef
        # the method without the last (length(rawargs) - k + 1) arguments
        taken = full[1:k-1]
        callargs = Any[names[1:k-1]..., Any[rawargs[j].args[2] for j in k:length(rawargs)]...]
        call = isempty(kwforward) ? Expr(:call, fname, callargs...) : Expr(:call, fname, kwforward[1], callargs...)
        push!(defs, Expr(:(=), _mksig(fname, taken, kwtake, nothing, wheres), call))
    end
    worker = nothing
    rest = Any[]
    for d in defs
        r = _rewrite_fdef(mod, d)
        if r === nothing
            push!(rest, d)
        elseif worker === nothing
            worker, rr = r
            append!(rest, rr)
        else
            w, rr = r
            push!(rest, w)
            append!(rest, rr)
        end
    end
    worker === nothing && return nothing
    return worker, rest
end

"`return x` in a `Like` body returns `like(t, x)`: the representation made a trait object like `t` (nested functions keep their own returns)."
function _like_returns(ex, t)
    ex isa Expr || return ex
    ex.head in (:function, :->, :quote) && return ex
    ex.head === :(=) && ex.args[1] isa Expr && ex.args[1].head === :call && return ex   # a short local function
    ex.head === :return && return Expr(:return, :($TraitWorld.like($t, $(_like_returns(isempty(ex.args) ? nothing : ex.args[1], t)))))
    return Expr(ex.head, Any[_like_returns(a, t) for a in ex.args]...)
end

function _rewrite_fdef(mod::Module, ex)
    ex = _dynamic_containers(mod, ex)
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
    likearg = nothing
    if ret isa Expr && ret.head === :curly && ret.args[1] in (:Like, :(TraitWorld.Like)) && length(ret.args) == 2
        # a result like the input: the body's value is a representation; the worker makes it a
        # trait object of the argument's implementation, the entry a value of the caller's type
        likearg = ret.args[2]
        ret = nothing
        body = :($TraitWorld.like($likearg, $(_like_returns(body, likearg))))
    end
    rawargs = sig.args[2:end]
    kwparams = Any[]
    if !isempty(rawargs) && rawargs[1] isa Expr && rawargs[1].head === :parameters
        kwparams = rawargs[1].args
        rawargs = rawargs[2:end]
    end
    unbounded = Symbol[w for w in wheres if w isa Symbol]
    args = [_classify(mod, a, unbounded) for a in rawargs]
    kws = [_classify_kw(mod, p, unbounded) for p in kwparams]
    istraitdef = any(x -> x.kind in (:trait, :callable, :callables, :vararg_trait), args) ||
                 any(x -> x.kind in (:trait, :callable), kws)
    if istraitdef && any(a -> a isa Expr && a.head === :kw, rawargs)
        return _expand_defaults(mod, head, fname, rawargs, kwparams, wheres, ret, body)
    end
    key = _fkey(mod, fname)
    pattern = Any[(x.kind in (:trait, :callable, :callables, :untyped, :vararg_trait)) ? nothing : x.ann for x in args]
    entries = _registry(mod, key, :__tw_entries__)
    plain = _registry(mod, key, :__tw_plain__)
    if !istraitdef
        # an untyped method shaped like an existing entry is that entry's fallback (keywords and defaults kept)
        if entries !== nothing && pattern in get(entries, key, Any[])
            s = _mksig(fname, Any[:(::$TraitWorld.Untyped), rawargs...], kwparams, ret, wheres)
            return Expr(head, s, body), Any[:($TraitWorld._check_methods(@__MODULE__, $(QuoteNode(fname))))]
        end
        plain === nothing || push!(get!(plain, key, Any[]), pattern)
        return ex, Any[:($TraitWorld._check_methods(@__MODULE__, $(QuoteNode(fname)))),
                       :($TraitWorld._check_entries_intact(@__MODULE__, $(QuoteNode(fname))))]
    end
    nva = count(x -> x.kind in (:vararg, :vararg_trait), args)
    nva <= 1 && (nva == 0 || args[end].kind in (:vararg, :vararg_trait)) ||
        error("@trait_module: `$fname` has a vararg that is not last")
    # --- the worker
    wargs = Any[]
    newwheres = Any[]
    function tobj_bound(x; perelement::Bool = false)
        T = gensym(:T)
        fams = Any[]
        closure = Any[]
        # a vararg's elements may differ in representation: each is its own existential type
        wl = perelement ? Any[] : newwheres
        # every trait, and its supertraits, as a pattern with a type variable for each open
        # parameter (the representation included): `TT >: Union{ColTable{R1}, ArrayLike{Float64, N1, R2}}`
        for X in x.traits
            F = _family(X)
            for Y in trait_closure(F)
                any(z -> z === Y, fams) && continue
                push!(fams, Y)
                # the family and a tag per parameter the bound fixes: no free type variable (see `PTag`)
                append!(closure, Any[_bound_members(Y === F ? X : Y)...])
            end
        end
        push!(wl, Expr(:(>:), T, Expr(:curly, :Union, closure...)))
        perelement && return Expr(:where, :($TraitWorld.TObj{$T}), wl...)
        return :($TraitWorld.TObj{$T})
    end
    for x in args
        if x.kind === :trait
            push!(wargs, :($(x.name)::$(tobj_bound(x))))
        elseif x.kind === :vararg_trait
            push!(wargs, Expr(:..., :($(x.name)::$(tobj_bound(x; perelement = true)))))
        elseif x.kind === :callable
            push!(wargs, :($(x.name)::$TraitWorld.CObj{$(x.A),$(x.S)}))
        elseif x.kind === :callables
            cs = [:($TraitWorld.CObj{$A,$S}) for (A, S, _) in x.traits]
            push!(wargs, :($(x.name)::$TraitWorld.CMulti{<:Tuple{$(cs...)}}))
        elseif x.kind === :untyped
            push!(wargs, x.name)
        elseif x.kind === :vararg
            push!(wargs, x.name)                      # as written, `xs::Int...` or `xs...`
        else
            push!(wargs, x.ann === nothing ? x.name : :($(x.name)::$(x.ann)))
        end
    end
    wkws = Any[]
    for x in kws
        if x.kind === :kwrest
            push!(wkws, Expr(:..., x.name))
            continue
        end
        lhs = x.kind === :trait ? :($(x.name)::$TraitWorld.TObj) :
              x.kind === :callable ? :($(x.name)::$TraitWorld.CObj{$(x.A),$(x.S)}) :
              x.ann === nothing ? x.name : :($(x.name)::$(x.ann))
        push!(wkws, x.required ? lhs : Expr(:kw, lhs, x.default))
    end
    if likearg !== nothing
        any(x -> x.kind === :trait && x.name === likearg, args) ||
            error("@trait_module: `::Like{$likearg}` names no trait-bounded argument of `$fname`")
    end
    wsig = _mksig(fname, wargs, wkws, ret, Any[wheres..., newwheres...])
    worker = Expr(head, wsig, body)
    rest = Any[]
    likearg === nothing || push!(rest, :($TraitWorld._like!($fname)))
    # --- the entry, once per shape
    existing = entries === nothing ? Any[] : get(entries, key, Any[])
    if !(pattern in existing)
        if plain !== nothing && pattern in get(plain, key, Any[])
            error("@trait_module: `$fname` already has an untyped method of the shape its trait-bounded method needs " *
                  "for an entry; define the trait-bounded methods first, then the untyped fallback")
        end
        if key[1] !== mod
            # an entry is a method at Any: only the function's owner may add one (rule 3)
            owner(key[1]) === owner(mod) || error("@trait_module: `$fname` belongs to $(key[1]); $(mod) may add trait-bounded " *
                                                  "methods to it only where it already has an entry of that shape (rule 3)")
        end
        nargs = nva == 0 ? length(args) : -1
        eargs = Any[]
        stmts = Any[]
        callnames = Any[]
        for x in args
            nm = x.name
            if x.kind in (:trait, :callable, :callables)
                push!(eargs, :(@nospecialize($nm)))
                push!(callnames, nm)
            elseif x.kind === :vararg_trait
                push!(eargs, :(@nospecialize($nm...)))
                push!(callnames, Expr(:..., nm))
            elseif x.kind === :vararg
                push!(eargs, x.ann)                   # as written
                push!(callnames, Expr(:..., nm))
            elseif x.kind === :untyped
                push!(eargs, nm)
                push!(callnames, nm)
            else
                push!(eargs, x.ann === nothing ? nm : :($nm::$(x.ann)))
                push!(callnames, nm)
            end
        end
        haskw = !isempty(kws)
        kwname = gensym(:kws)
        ntname = gensym(:nt)
        haskw && push!(stmts, :($ntname = Base.values($kwname)))
        newnames = Any[]
        for (i, x) in enumerate(args)
            if x.kind === :trait
                v = gensym(Symbol(x.name, :_view))
                push!(stmts, :($v = $TraitWorld.enter($TraitWorld.EntryPos{typeof($fname),$i,$nargs}(), $(x.name))))
                fb = haskw ? :($TraitWorld.kwfallback($ntname, $fname, $(callnames...))) : :($TraitWorld.fallback($fname, $(callnames...)))
                push!(stmts, :($v === $TraitWorld.NOTRAIT && return $fb))
                push!(newnames, v)
            elseif x.kind === :vararg_trait
                v = gensym(Symbol(x.name, :_views))
                push!(stmts, :($v = $TraitWorld.enter_each($TraitWorld.EntryPos{typeof($fname),$i,-1}(), $(x.name))))
                fb = haskw ? :($TraitWorld.kwfallback($ntname, $fname, $(callnames...))) : :($TraitWorld.fallback($fname, $(callnames...)))
                push!(stmts, :($v === $TraitWorld.NOTRAIT && return $fb))
                push!(newnames, Expr(:..., v))
            elseif x.kind === :callable
                v = gensym(Symbol(x.name, :_fn))
                push!(stmts, :($v = $TraitWorld.enter_callable($(x.A), $(x.S), $(x.M === nothing ? :nothing : x.M), $(x.name))))
                push!(newnames, v)
            elseif x.kind === :callables
                v = gensym(Symbol(x.name, :_fn))
                sigs = Expr(:tuple, [Expr(:tuple, A, S, M === nothing ? :nothing : M) for (A, S, M) in x.traits]...)
                push!(stmts, :($v = $TraitWorld.enter_callables($sigs, $(x.name))))
                push!(newnames, v)
            elseif x.kind === :vararg
                push!(newnames, Expr(:..., x.name))
            else
                push!(newnames, x.name)
            end
        end
        for x in kws
            x.kind in (:trait, :callable) || continue
            k = QuoteNode(x.name)
            if x.kind === :trait
                tl = :($TraitWorld.TraitList{Tuple{$(x.traits...)}}())
                push!(stmts, :($ntname = $TraitWorld.enter_kw($tl, $fname, $k, $ntname)))
            else
                push!(stmts, :($ntname = $TraitWorld.enter_kw_callable($(x.A), $(x.S), $(x.M === nothing ? :nothing : x.M), $k, $ntname)))
            end
        end
        # the result goes back through `_out`: a trait object like an argument becomes a value of its caller's type
        tr = [i for (i, x) in enumerate(args) if x.kind === :trait]
        us = Expr(:tuple, [args[i].name for i in tr]...)
        vs = Expr(:tuple, [newnames[i] for i in tr]...)
        # the tuples of the user's values and trait objects are built only for a result like the input:
        # built for every call, they instantiate a tuple type at run time in an entry compiled at `Any`
        # (about 140 ns and 80 bytes per untyped call)
        res = gensym(:res)
        if haskw
            push!(stmts, :($res = $TraitWorld.checked_kwcall($ntname, $fname, $(newnames...))))
        else
            push!(stmts, :($res = $TraitWorld.checked_call($fname, $(newnames...))))
        end
        push!(stmts, :(return $res isa $TraitWorld.LikeResult ? Base.inferencebarrier($TraitWorld._like_out)($res, $us, $vs) : $res))
        kept = Any[w for w in wheres if any(x -> x.kind in (:plain, :vararg) && x.ann !== nothing && _uses(x.ann, _wherevar(w)), args)]
        esig = haskw ? Expr(:call, fname, Expr(:parameters, Expr(:..., kwname)), eargs...) : Expr(:call, fname, eargs...)
        isempty(kept) || (esig = Expr(:where, esig, kept...))
        # an ordinary method, inlined into a typed caller (keys-plan §6): there it runs at plain speed.
        # It is the boundary (rule 2): compiled in its caller's mode, while the worker it calls is
        # compiled by facts (`Expr(:meta, :facts, 0)`, read by Julia's compiler)
        pushfirst!(stmts, Expr(:meta, :facts, 0))
        push!(rest, Expr(:macrocall, GlobalRef(Base, Symbol("@inline")), LineNumberNode(0, :none),
                         Expr(:function, esig, Expr(:block, stmts...))))
        if entries !== nothing
            push!(get!(entries, key, Any[]), pattern)
        end
    end
    push!(rest, :($TraitWorld._check_methods(@__MODULE__, $(QuoteNode(fname)))))
    # the traits each trait position needs: fixed when the module is complete, updated by later definitions
    nargs_w = nva == 0 ? length(args) : -1
    for (i, x) in enumerate(args)
        x.kind in (:trait, :vararg_trait) || continue
        push!(rest, :($TraitWorld._note_position(@__MODULE__, $fname, $i, $(x.kind === :vararg_trait ? -1 : nargs_w))))
    end
    key[1] !== mod && isdefined(mod, :__tw_extended__) && push!(mod.__tw_extended__, key)
    push!(rest, :($TraitWorld._bump!()))
    return worker, rest
end

# --- checks ----------------------------------------------------------------------

"Rule 3: every method a trait module defines is owned by its package, in every signature it applies to."
function _check_methods(mod::Module, fname)
    f = Core.eval(mod, fname)
    seen = isdefined(mod, :__tw_methods_seen__) ? mod.__tw_methods_seen__ : Base.IdSet{Method}()
    for m in methods(f)
        m.module === mod || continue
        m in seen && continue            # each method is checked once, not at every later definition
        push!(seen, m)
        owned_method(m) && continue
        throw(OwnershipError("$(m) is defined by $(mod), which owns neither its function nor its types " *
                             "in every signature it applies to (rule 3)"))
    end
    return nothing
end

"An ordinary method must never take an entry's place (same signature): that would silently switch the trait methods off."
function _check_entries_intact(mod::Module, fname)
    f = Core.eval(mod, fname)
    f isa Function || return nothing
    key = (parentmodule(f), nameof(f))
    entries = _registry(mod, key, :__tw_entries__)
    entries === nothing && return nothing
    n = length(get(entries, key, Any[]))
    have = count(_is_entry, methods(f))
    have >= n || throw(TraitBoundError("a method of `$fname` defined in $mod replaced the entry of its trait-bounded methods " *
                                       "(it has the entry's signature). Give its arguments types, or write it untyped " *
                                       "after the trait-bounded methods, so it becomes their fallback."))
    return nothing
end

"""
A trait position of an entry, noted where its worker is defined. Once the module is
complete, `needed` is fixed for it; a definition after that (at the prompt) updates it.
"""
function _note_position(mod::Module, @nospecialize(f), pos::Int, nargs::Int)
    isdefined(mod, :__tw_positions__) || return nothing
    k = (f, pos, nargs)
    any(x -> x[1] === f && x[2] == pos && x[3] == nargs, mod.__tw_positions__) || push!(mod.__tw_positions__, k)
    mod.__tw_finished__[] && (_fix_needed!(mod, f, pos, nargs); _fix_keeps!(mod, f))
    return nothing
end

"""
Define `needed(EntryPos{typeof(f), pos, nargs})` in `mod`: the traits the workers of `f` need
there, as a constant, so that an entry folds for a known type. Redefined only when they change.
"""
function _fix_needed!(mod::Module, @nospecialize(f), pos::Int, nargs::Int)
    P = EntryPos{typeof(f),pos,nargs}
    L = Tuple{traits_at(f, pos, nargs)...}
    m = Base._which(Tuple{typeof(needed),P}; raise = false)
    if m !== nothing && Base.unwrap_unionall(m.method.sig).parameters[2] === P
        typeof(Base.invokelatest(needed, P())).parameters[1] == L && return nothing
        m.method.module === mod || ccall(:jl_generating_output, Cint, ()) == 0 || throw(TraitBoundError(
            "$mod adds bounds to `$f`, whose entry belongs to $(m.method.module): while a package is built, " *
            "only the entry's own module may change what its positions need"))
    end
    Core.eval(mod, :($TraitWorld.needed(::$P) = $TraitWorld.TraitList{$L}()))
    return nothing
end

"""
At the end of a trait module: the entry positions' needs are fixed, and every pair of
workers whose bounds at a position are unrelated needs a worker with both bounds.
"""
function _finish_module(mod::Module)
    if isdefined(mod, :__tw_positions__)
        for (f, pos, nargs) in mod.__tw_positions__
            _fix_needed!(mod, f, pos, nargs)
        end
        for f in unique(Any[x[1] for x in mod.__tw_positions__])
            _fix_keeps!(mod, f)
        end
        mod.__tw_finished__[] = true
    end
    _refuse_overrides()
    isdefined(mod, :__tw_entries__) || return nothing
    # this module's functions, and other modules' functions it gave workers to
    ks = Any[k for k in keys(mod.__tw_entries__) if k[1] === mod]
    isdefined(mod, :__tw_extended__) && append!(ks, collect(mod.__tw_extended__))
    for key in unique(ks)
        isdefined(key[1], key[2]) || continue
        f = getfield(key[1], key[2])
        check_bounds(f)
        check_entry_ambiguities(f)
    end
    # definition checking (note "Definition checking"): every bounded method once, at archetypes,
    # where it is defined; a mistake is reported at its line before any type conforms. At a
    # package's build it is an error; for trait code defined at the prompt a warning (the call
    # raises it again), so that interactive work can pass through incomplete code
    if _DEFCHECK_AT_END[]
        if ccall(:jl_generating_output, Cint, ()) == 1
            check_definitions(mod)
        else
            ps = try check_definitions(mod) catch e; e isa TraitUseError ? e.problems : rethrow() end
            isempty(ps) || @warn "trait module $(nameof(mod)): library code breaks a rule of the trait world:\n  " * join(ps, "\n  ")
        end
    end
    return nothing
end
"Whether a trait module's end checks its definitions (`JULIA_TW_DEFCHECK=0` turns it off, for measurement)."
const _DEFCHECK_AT_END = Ref(true)

_isworker(m::Method) = any(p -> _tobj_lb(p) !== nothing, Base.unwrap_unionall(m.sig).parameters[2:end])

"""
Types first, then traits: an entry (at `Any` in its trait positions) and a
type-annotated method can still be ambiguous when they differ in other
positions, `f(t::ColTable, x::Int)` against `f(v::AbstractVector, x::Integer)`.
Reported when the function is defined, not when a call happens to hit it.
"""
function check_entry_ambiguities(@nospecialize(f))
    ms = collect(methods(f))
    problems = String[]
    for i in 1:length(ms), j in i+1:length(ms)
        (_isworker(ms[i]) && _isworker(ms[j])) && continue      # workers: check_bounds
        # two entries that differ in which position is trait-bounded overlap only where a value
        # has a projection in both: a call there raises Julia's own ambiguity error
        (_is_entry(ms[i]) && _is_entry(ms[j])) && continue
        Base.isambiguous(ms[i], ms[j]) && push!(problems, "$(ms[i])\n    and $(ms[j])")
    end
    isempty(problems) || throw(TraitBoundError("ambiguous methods of `$f`:\n  " * join(problems, "\n  ") *
                                               "\nAdd a method for their intersection."))
    return nothing
end

"A trait bound as members of a worker's lower bound: its family, and `PTag{F, i, v}` for each parameter it fixes."
function _bound_members(@nospecialize(X))
    u = Base.unwrap_unionall(X)
    fam = u.name.wrapper
    out = Any[fam]
    ps = u.parameters
    for i in 1:length(ps)-1
        ps[i] isa TypeVar || push!(out, PTag{fam,i,ps[i]})
    end
    return out
end

"""
A trait bound as a pattern for a worker's signature: the family applied to the
parameters the bound fixes and a fresh type variable for each open one,
including the representation; the variables are added to `wheres`.
"""
function _pattern_expr!(@nospecialize(X), wheres::Vector{Any})
    u = Base.unwrap_unionall(X)
    fam = u.name.wrapper
    args = Any[]
    for p in u.parameters
        if p isa TypeVar
            s = gensym(p.name)
            push!(wheres, s)
            push!(args, s)
        else
            push!(args, p)
        end
    end
    return Expr(:curly, fam, args...)
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
                push!(bs, unique(_family.(Base.uniontypes(lb))))
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
