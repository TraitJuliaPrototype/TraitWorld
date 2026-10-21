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
                  :(const __tw_attrs__ = Dict{Any,Symbol}()), # (function, position, nargs) => the attribute a bound declares there
                  :(const __tw_untyped__ = Any[]),            # (function, nargs, method object, trait positions) of tabled entries (untyped.jl)
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
    elseif h === :macrocall && _part_concrete_level(ex.args[1]) !== nothing && _prefixed_fdef(ex.args[end]) !== nothing
        # @enforce_concrete_only / @warn_on_abstract names… on one function (traits reference §11.2)
        names = Any[a for a in ex.args[2:end-1] if !(a isa LineNumberNode)]
        all(a -> a isa Symbol, names) && !isempty(names) ||
            error("@trait_module: `$(ex.args[1])` before a function names its bounded arguments or the `where` variables its bounds name (traits reference §11.2)")
        return Base.ScopedValues.with(_PART_CONCRETE => (_part_concrete_level(ex.args[1]), Symbol[names...])) do
            _process(mod, ex.args[end])
        end
    elseif h === :macrocall && _fully_typed_macro_level(ex.args[1]) !== nothing && _prefixed_fdef(ex.args[end]) !== nothing
        # @warn_not_fully_typed / @enforce_fully_typed on one function: fully typed mode (traits reference §11.3)
        level = _fully_typed_macro_level(ex.args[1])
        inner = ex.args[end]
        fname = _fdef_name(_prefixed_fdef(inner))
        r = _process(mod, inner)
        return Expr(:toplevel, r, :($TraitWorld.fully_typed_level(::typeof($fname)) = $(QuoteNode(level))))
    elseif h === :struct
        st, ctor = _bounded_struct(mod, _dynamic_fields(mod, ex))
        return ctor === nothing ? st : Expr(:toplevel, st, ctor)
    elseif h === :macrocall
        name = ex.args[1]
        inner = ex.args[end]
        if name == GlobalRef(Core, Symbol("@doc")) && inner isa Expr && inner.head === :struct
            st, ctor = _bounded_struct(mod, _dynamic_fields(mod, inner))
            d = Expr(:macrocall, ex.args[1:end-1]..., st)
            return ctor === nothing ? d : Expr(:toplevel, d, ctor)
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
A trait's name in a struct field or a container means a value of the trait with its attribute,
as an abstract type's name there means a boxed value (traits reference §7): `plots::Vector{Plot}`
is `Vector{Kept{Plot}}`, `bg::ColorSpec` is `Kept{ColorSpec}`, each item `Compiled{X}` or
`Dynamic{X}` as it was stored. `Vector{<:ColTable}` keeps its meaning, one representation.
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

"""
Whether `B`, a struct parameter's upper bound, names a trait or `Callable` (an instance of either,
possibly naming the struct's other parameters): a parameter bounded by a trait.
"""
function _istraitbound(mod::Module, B)
    h = B isa Expr && B.head === :curly ? B.args[1] : B
    (h isa Symbol || (h isa Expr && h.head === :.)) || return false
    v = _tryeval(mod, h)
    return v === Callable || (v isa Type && is_trait(v))
end
"The name a struct parameter declares (`T`, `T <: Real`)."
_paramname(p) = p isa Expr && p.head === :(<:) ? p.args[1] : p

"""
A struct with parameters bounded by a trait (traits reference §7.4, lowering §13.2): the bounds
stripped from its header (a trait is not a Julia type), Julia's constructor with explicit parameters
kept as it is, and the constructor without parameters an entry for the bounded fields: each field
typed exactly by a bounded parameter takes that parameter's bound, where the caller's cast or the
first-seen rule applies, and the parameter becomes the stored form's type (the user's object for a
`Compiled` value, `Dynamic{X}` for a `Dynamic` one). Returns the struct and that constructor, or
`nothing` for a struct without such parameters.
"""
function _bounded_struct(mod::Module, ex::Expr)
    header = ex.args[2]
    sup = header isa Expr && header.head === :(<:) ? header.args[2] : nothing
    h = sup === nothing ? header : header.args[1]
    h isa Expr && h.head === :curly || return ex, nothing
    bounds = Dict{Symbol,Any}()
    params = Any[]
    for p in h.args[2:end]
        if p isa Expr && p.head === :(<:) && length(p.args) == 2 && p.args[1] isa Symbol && _istraitbound(mod, p.args[2])
            bounds[p.args[1]] = p.args[2]
            push!(params, p.args[1])
        else
            push!(params, p)
        end
    end
    isempty(bounds) && return ex, nothing
    name = h.args[1]
    nh = Expr(:curly, name, params...)
    pnames = Any[_paramname(p) for p in params]
    nfields = count(f -> !(f isa LineNumberNode), ex.args[3].args)
    fsyms = [gensym(:f) for _ in 1:nfields]
    # Julia's constructor with explicit parameters, written out: a struct with an inner constructor gets no
    # default outer one, whose place the bound's constructor below takes
    inner = Expr(:function, Expr(:where, Expr(:call, Expr(:curly, name, pnames...), fsyms...), params...),
                 Expr(:block, Expr(:call, Expr(:curly, :new, pnames...), fsyms...)))
    st = Expr(:struct, ex.args[1], sup === nothing ? nh : Expr(:(<:), nh, sup), Expr(:block, ex.args[3].args..., inner))
    fields = Tuple{Symbol,Any}[]
    for f in ex.args[3].args
        f isa LineNumberNode && continue
        g = f isa Expr && f.head === :const ? f.args[1] : f
        if g isa Symbol
            push!(fields, (g, :Any))
        elseif g isa Expr && g.head === :(::) && g.args[1] isa Symbol
            push!(fields, (g.args[1], g.args[2]))
        else
            error("@trait_module: struct $name has parameters bounded by a trait, so its constructor is the bound's; " *
                  "an inner constructor is not allowed (yet). Write an outer constructor that calls `$name(…)`")
        end
    end
    names = Symbol[_paramname(p) for p in params]
    args = Any[]; stmts = Any[Expr(:meta, :facts_boundary), Expr(:meta, :inline)]
    vals = Any[]; ptype = Dict{Symbol,Any}()
    for (fname, ft) in fields
        if ft isa Symbol && haskey(bounds, ft)
            haskey(ptype, ft) && error("@trait_module: struct $name: the bounded parameter `$ft` types two fields; it may type one")
            k = gensym(fname)
            push!(args, Expr(:macrocall, Symbol("@nospecialize"), LineNumberNode(0), fname))   # as an entry's: compiled at `Any` for a caller that does not know the type
            push!(stmts, :($k = $TraitWorld._kept_at($(bounds[ft]), $fname, Val($TraitWorld._known_type($fname)))))
            push!(vals, k)
            ptype[ft] = :(typeof($k))
        else
            any(F -> _uses(ft, F), keys(bounds)) &&
                error("@trait_module: struct $name: field `$fname` uses a bounded parameter inside another type; a bounded parameter may only type a field itself")
            push!(args, :($fname::$ft))
            push!(vals, fname)
        end
    end
    for F in keys(bounds)
        haskey(ptype, F) || error("@trait_module: struct $name: the bounded parameter `$F` types no field")
    end
    free = Any[p for p in params if !haskey(bounds, _paramname(p))]
    for p in free
        any(((_, ft),) -> !(ft isa Symbol && haskey(bounds, ft)) && _uses(ft, _paramname(p)), fields) ||
            error("@trait_module: struct $name: parameter `$(_paramname(p))` is named by no field outside a bound, so its constructor cannot determine it")
    end
    push!(stmts, :(return $name{$([haskey(ptype, n) ? ptype[n] : n for n in names]...)}($(vals...))))
    sig = Expr(:call, name, args...)
    isempty(free) || (sig = Expr(:where, sig, free...))
    ctor = Expr(:function, sig, Expr(:block, stmts...))
    return st, Expr(:toplevel, ctor, :($TraitWorld.bounded_constructor(::Type{<:$name}) = true))
end

"""
A type with each trait's name in it (and `Callable{A, S}`) made `Kept{X}`, the one spelling of a
value kept with its attribute; `Dynamic{X}` and `Compiled{X}` written out stay the plain types
(traits reference §7). In an argument's type (`arg`), a trait's name as a parameter is
`<:HeldValue{X}`: Julia's parameters are invariant, so `cs::Vector{Column}` takes a
`Vector{Dynamic{Column}}`, a `Vector{Compiled{Column}}` and a `Vector{Kept{Column}}` alike.
"""
function _dyn_type(mod::Module, T, arg::Bool = false, inner::Bool = false)
    kept(X) = arg && inner ? Expr(:(<:), :($TraitWorld.HeldValue{$X})) : :($TraitWorld.Kept{$X})
    _iskepttype(mod, T) && return T                          # `Kept{X}`, `HeldValue{X}`: already the storage type
    T isa Expr && T.head === :curly && (h0 = _tryeval(mod, T.args[1]); h0 === Dynamic || h0 === Compiled) && return T
    if T isa Symbol || (T isa Expr && T.head === :.)
        v = _tryeval(mod, T)
        return (v isa Type && is_trait(v)) ? kept(T) : T
    elseif T isa Expr && T.head === :curly
        h = _tryeval(mod, T.args[1])
        ((h === Callable && (inner || !arg)) || (h isa Type && is_trait(h))) && return kept(T)   # `f::Callable{…}` on an argument stays a bound
        return Expr(:curly, T.args[1], Any[(a isa Expr && a.head === :(<:)) ? a : _dyn_type(mod, a, arg, true) for a in T.args[2:end]]...)
    end
    return T
end

"""
A trait's name as a container's element type in a function means a value of the trait with its
attribute (`Kept{X}`), as in a field (note "Traits as abstract types"): `Column[]`, `Column[a, b]`, `Vector{Column}(undef, n)`
and `Dict{String, Column}()` in a body; `cs::Vector{Column}` in an argument. A trait's name in
an argument itself stays a bound, and `Vector{<:ColTable}` keeps its meaning.
"""
function _dynamic_containers(mod::Module, ex::Expr)
    sig, body = ex.args[1], ex.args[2]
    return Expr(ex.head, _dyn_sig(mod, sig), _dyn_body(mod, body))
end
"Whether `x` names `Dynamic` or `Compiled`: an attribute on a bound (traits reference §5.1)."
_isattribute(mod::Module, x) = (x isa Symbol || (x isa Expr && x.head === :.)) && (v = _tryeval(mod, x); v === Dynamic || v === Compiled)
"Whether `T` is `Kept{X}` or `HeldValue{X}` written out: the storage type itself."
_iskepttype(mod::Module, T) = T isa Expr && T.head === :curly && (h = _tryeval(mod, T.args[1]); h === Kept || h === HeldValue)
"Whether type expression `T` names `Dynamic{X}` or `Compiled{X}` anywhere."
_has_attributed(mod::Module, T) = _isattributed(mod, T) || (T isa Expr && any(a -> _has_attributed(mod, a), T.args))
"Whether `x` is `Dynamic{X}` or `Compiled{X}` written out."
_isattributed(mod::Module, x) = x isa Expr && x.head === :curly && length(x.args) == 2 && _isattribute(mod, x.args[1])
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
    elseif a.head === :(::) && length(a.args) == 2 && a.args[2] isa Expr && a.args[2].head === :curly && _isattribute(mod, a.args[2].args[1])
        return a                                     # `x::Dynamic{X}`, `x::Compiled{X}`: a bound with an attribute
    elseif a.head === :(::) && length(a.args) == 2 && a.args[2] isa Expr && a.args[2].head === :curly && !_istraitname(mod, a.args[2].args[1])
        return Expr(:(::), a.args[1], _dyn_type(mod, a.args[2], true))
    elseif a.head === :(::) && length(a.args) == 2 && a.args[2] isa Expr && (a.args[2].head === :curly || a.args[2].head === :tuple)
        return Expr(:(::), a.args[1], _dyn_bound(mod, a.args[2]))
    end
    return a
end
"""
A bound's parameters are types, values of the trait's associated types: a trait's name there is an
item position (traits reference §8.2), `xs::Iterable{Shape}`, items seen through `Shape`, each
`Compiled` or `Dynamic` by its type; `Iterable{Compiled{Shape}}` and `Iterable{Dynamic{Shape}}` set
the attribute. Lowered to `Through{Shape, A}` (`:default`, `:compiled`, `:dynamic`), also inside
another parameter (`Pair{String, Shape}`). The bound's own name stays a bound.
"""
function _dyn_bound(mod::Module, b::Expr)
    b.head === :tuple && return Expr(:tuple, Any[(x isa Expr && x.head === :curly) ? _dyn_bound(mod, x) : x for x in b.args]...)
    _istraitname(mod, b.args[1]) || return b
    return Expr(:curly, b.args[1], Any[(p isa Expr && p.head === :(<:)) ? p : _item_param(mod, p) for p in b.args[2:end]]...)
end
"An item parameter: a trait's name, or `Compiled{X}`/`Dynamic{X}`, as `Through{X, A}`; inside a type's parameters too."
function _item_param(mod::Module, p)
    if _istraitname(mod, p)
        return :($TraitWorld.Through{$p, :default})
    elseif p isa Expr && p.head === :curly && length(p.args) == 2 && _isattribute(mod, p.args[1]) && _istraitname(mod, p.args[2])
        a = _tryeval(mod, p.args[1]) === Compiled ? :compiled : :dynamic
        return :($TraitWorld.Through{$(p.args[2]), $(QuoteNode(a))})
    elseif p isa Expr && p.head === :curly && _iskepttype(mod, p)
        error("@trait_module: an item parameter is a trait's name, `Compiled{X}` or `Dynamic{X}`; `$p` is not one " *
              "(items keep their attribute: write the trait's name)")
    elseif p isa Expr && p.head === :curly
        return Expr(:curly, p.args[1], Any[(q isa Expr && q.head === :(<:)) ? q : _item_param(mod, q) for q in p.args[2:end]]...)
    end
    return p
end
function _dyn_body(mod::Module, x)
    x isa Expr || return x
    x.head in (:quote, :inert, :meta) && return x
    if x.head in (:ref, :typed_vcat, :typed_hcat, :typed_comprehension) && _istraitname(mod, x.args[1])
        return Expr(x.head, :($TraitWorld.Kept{$(x.args[1])}), Any[_dyn_body(mod, a) for a in x.args[2:end]]...)
    elseif x.head === :curly && (_isattribute(mod, x.args[1]) || _iskepttype(mod, x))
        return x                                     # `Dynamic{X}(t)`, `::Compiled{X}`, `Kept{X}(t)`: a type, not storage
    elseif x.head === :(::) && length(x.args) == 2 && _has_attributed(mod, x.args[2])
        return Expr(:(::), _dyn_body(mod, x.args[1]), x.args[2])   # a type assertion: written as it is meant, not storage
    elseif x.head === :curly && !_istraitname(mod, x.args[1]) && any(a -> _istraitname(mod, a), x.args[2:end])
        return _dyn_type(mod, x)
    end
    return Expr(x.head, Any[_dyn_body(mod, a) for a in x.args]...)
end

"The concreteness of the parts a function's prefix names (traits reference §11.2), while its definition is rewritten: `(level, names)`."
const _PART_CONCRETE = Base.ScopedValues.ScopedValue{Any}(nothing)
"A function definition, under any concreteness prefixes; else `nothing`."
function _prefixed_fdef(ex)
    while ex isa Expr && ex.head === :macrocall && (_part_concrete_level(ex.args[1]) !== nothing || _fully_typed_macro_level(ex.args[1]) !== nothing)
        ex = ex.args[end]
    end
    return _is_fdef(ex) ? ex : nothing
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
    M::Any          # the attribute the bound names, `:compiled` or `:dynamic`, or nothing (the default rule)
    default::Any    # a keyword's default, or nothing
    required::Bool  # a keyword without a default
end
_Arg(name, ann, kind, traits, A, S, M) = _Arg(name, ann, kind, traits, A, S, M, nothing, false)

"The parameters of a `Callable` bound, `Callable{A, S}`, with an attribute (`Compiled{Callable{A, S}}`, `Dynamic{Callable{A, S}}`): `(A, S, M)`, `M` the attribute or `nothing`."
function _callable_params(@nospecialize(v))
    M = nothing
    if v isa DataType && (v.name === Base.typename(Compiled) || v.name === Base.typename(Dynamic))
        M = v.name === Base.typename(Compiled) ? :compiled : :dynamic
        v = v.parameters[1]
    end
    v isa Type && v !== Union{} && v <: Callable || return nothing
    u = Base.unwrap_unionall(v)
    u isa DataType && u.name === Base.typename(Callable) || return nothing
    A, S = u.parameters
    (A isa TypeVar || S isa TypeVar) && return nothing
    return (A, S, M)
end
"A trait bound with an attribute, `Compiled{X}` or `Dynamic{X}`: `(X, :compiled)` or `(X, :dynamic)`, else `nothing`."
function _attributed_bound(@nospecialize(v))
    v isa DataType && (v.name === Base.typename(Compiled) || v.name === Base.typename(Dynamic)) || return nothing
    X = v.parameters[1]
    is_trait(X) || return nothing
    return (X, v.name === Base.typename(Compiled) ? :compiled : :dynamic)
end

function _classify(mod::Module, a, unbounded::Vector{Symbol} = Symbol[]; attr_bounds::Bool = true, wheres::Vector{Any} = Any[])
    if a isa Expr && a.head === :macrocall && a.args[1] === Symbol("@specialize")
        error("@trait_module: `@specialize` is retired; write the attribute in the bound, `f::Compiled{Callable{A, S}}`, " *
              "or let the caller choose with `compiled_for(f)`")
    end
    if a isa Symbol
        return _Arg(a, nothing, :untyped, Any[], nothing, nothing, nothing)
    elseif a isa Expr && a.head === :...
        inner = _classify(mod, a.args[1], unbounded; attr_bounds, wheres)
        inner.kind === :trait && return _Arg(inner.name, inner.ann, :vararg_trait, inner.traits, nothing, nothing, inner.M)
        inner.kind in (:callable, :callables) && error("@trait_module: a vararg of `Callable` is not supported")
        return _Arg(a, nothing, :vararg, Any[], nothing, nothing, nothing)
    elseif a isa Expr && a.head === :kw
        x = _classify(mod, a.args[1], unbounded; attr_bounds, wheres)
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
        if attr_bounds && ann isa Expr && ann.head === :curly && length(ann.args) == 2 &&
           ann.args[2] isa Expr && ann.args[2].head === :tuple
            # an attribute on several bounds, `Dynamic{(ColTable, RowTable)}` (traits reference §5.1): read
            # from the syntax, since a tuple of traits is not a type parameter
            h = _tryeval(mod, ann.args[1])
            if h === Compiled || h === Dynamic
                attr = h === Compiled ? :compiled : :dynamic
                traits = Any[]
                for x in ann.args[2].args
                    v = _tryeval(mod, x)
                    is_trait(v) || error("@trait_module: `$x` in the bound `$ann` is not a trait")
                    _check_dynamic_params(v, attr, name)
                    append!(traits, bound_traits(v))
                end
                return _Arg(name, ann, :trait, traits, nothing, nothing, attr)
            end
        end
        v = _tryeval(mod, ann)
        if v === nothing && ann isa Expr && ann.head === :curly
            # a bound that names a method's `where` variables (traits reference §5.1): evaluated with them open
            used = Any[w for w in wheres if _uses(ann, _wherevar(w))]
            if !isempty(used)
                h = _tryeval(mod, ann.args[1])
                (h === Callable || h === Compiled || h === Dynamic) && _callable_args_use(mod, ann, used) &&
                    error("@trait_module: argument `$name`: a `Callable` bound's argument types are a constant type; `$ann` names " *
                          "the method's `where` variables. Write one method per signature (traits reference §5.8)")
                v = _tryeval(mod, Expr(:where, ann, used...))
                v isa Type && is_trait(v) && return _Arg(name, ann, :trait, bound_traits(v), nothing, nothing, nothing)
            end
        end
        cp = _callable_params(v)
        # in a method of an operation's function, `Dynamic{X}` is a type (traits reference §3.1)
        ab = attr_bounds ? _attributed_bound(v) : nothing
        if cp !== nothing
            return _Arg(name, ann, :callable, Any[], cp[1], cp[2], cp[3])
        elseif ab !== nothing
            _check_dynamic_params(ab[1], ab[2], name)
            return _Arg(name, ann, :trait, bound_traits(ab[1]), nothing, nothing, ab[2])
        elseif is_trait(v)
            return _Arg(name, ann, :trait, bound_traits(v), nothing, nothing, nothing)
        end
        return _Arg(name, ann, :plain, Any[], nothing, nothing, nothing)
    end
    return _Arg(a, nothing, :plain, Any[], nothing, nothing, nothing)
end

"Whether argument `a` is bounded by a trait whose parameters name the `where` variable `w` (`prob::ODEProblemTrait{T}`)."
function _bound_names(mod::Module, a, w)
    a isa Expr && a.head === :kw && (a = a.args[1])
    a isa Expr && a.head === :(::) && length(a.args) == 2 || return false
    ann = a.args[2]
    ann isa Expr && ann.head === :curly || return false
    h = _tryeval(mod, ann.args[1])
    return h isa Type && is_trait(h) && _uses(ann, _wherevar(w))
end
"Whether the `Callable` in bound `ann` (or under an attribute) names one of the `where` variables `used` in its argument types `A`."
function _callable_args_use(mod::Module, ann, used)
    ann isa Expr && ann.head === :curly || return false
    if _tryeval(mod, ann.args[1]) === Callable
        length(ann.args) >= 2 || return false
        return any(w -> _uses(ann.args[2], _wherevar(w)), used)
    end
    return any(a -> _callable_args_use(mod, a, used), ann.args[2:end])
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
    unbounded = Symbol[w for w in wheres if w isa Symbol && !any(a -> _bound_names(mod, a, w), rawargs)]
    attr_bounds = !_is_operation_function(mod, fname)
    args = [_classify(mod, a, unbounded; attr_bounds, wheres) for a in rawargs]
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
    pc = _PART_CONCRETE[]
    !istraitdef && pc !== nothing &&
        error("@trait_module: `$fname` has no bounded argument for `@enforce_concrete_only`/`@warn_on_abstract` to name (traits reference §11.2)")
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
    # `where` variables named in bounds (traits reference §5.1): read from the values' parameters at the
    # start of the body, or checked against the value something else fixes for them
    wbind = Any[]
    for x in args
        x.kind === :trait && x.ann isa Expr && x.ann.head === :curly || continue
        h = _tryeval(mod, x.ann.args[1])
        h isa Type && is_trait(h) || continue
        for (i, p) in enumerate(x.ann.args[2:end])
            if p isa Symbol && any(w -> _wherevar(w) === p, wheres)
                push!(wbind, (p, x.name, _family(h), i))
            elseif any(w -> _uses(p, _wherevar(w)), wheres)
                error("@trait_module: argument `$(x.name)`: a bound names a `where` variable only as a whole parameter, `$(x.ann.args[1]){…, T, …}`; `$p` is not one")
            end
        end
    end
    elsewhere(v) = any(x -> x.kind !== :trait && x.ann !== nothing && _uses(x.ann, v), args) ||
                   any(x -> x.ann !== nothing && x.kind !== :trait && _uses(x.ann, v), kws) ||
                   any(w -> _wherevar(w) !== v && _uses(w, v), wheres)
    boundonly = unique(Symbol[v for (v, _, _, _) in wbind if !elsewhere(v)])
    ret !== nothing && any(v -> _uses(ret, v), boundonly) &&
        error("@trait_module: `$fname`'s result type names a `where` variable that only a bound fixes; assert the result in the body instead")
    # the parts a concreteness prefix names (traits reference §11.2), checked at the body's start
    cchecks = Any[]
    if pc !== nothing
        lv, cnames = pc
        for n in cnames
            if any(x -> x.name === n && x.kind === :trait, args) || any(x -> x.name === n && x.kind === :trait, kws)
                push!(cchecks, :($TraitWorld._concrete_self($n, $(QuoteNode(lv)), $(QuoteNode(n)), $(QuoteNode(fname)))))
            elseif any(t -> t[1] === n, wbind)
                push!(cchecks, :($TraitWorld._concrete_part($n, $(QuoteNode(lv)), $(QuoteNode(n)), $(QuoteNode(fname)))))
            else
                error("@trait_module: `$fname`: `$n` is neither a bounded argument nor a `where` variable its bounds name (traits reference §11.2)")
            end
        end
    end
    if isempty(wbind)
        isempty(cchecks) || (body = Expr(:block, cchecks..., body))
    else
        prefix = Any[]
        seen = Symbol[]
        for (v, nm, F, i) in wbind
            val = :($TraitWorld._trait_param($nm, $F, Val($i)))
            if v in boundonly && !(v in seen)
                push!(prefix, :($v = $val))
                w = wheres[findfirst(w -> _wherevar(w) === v, wheres)]
                if w isa Expr && w.head === :(<:)
                    push!(prefix, :($v <: $(w.args[2]) || $TraitWorld._param_mismatch($(QuoteNode(nm)), $F, $i, $(QuoteNode(v)), $(w.args[2]), $v)))
                end
            else
                push!(prefix, :($val === $v || $TraitWorld._param_mismatch($(QuoteNode(nm)), $F, $i, $(QuoteNode(v)), $v, $val)))
            end
            push!(seen, v)
        end
        body = Expr(:block, prefix..., cchecks..., body)
        wheres = Any[w for w in wheres if !(_wherevar(w) in boundonly)]
    end
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
            owns(owner(mod), owner(key[1])) || error("@trait_module: `$fname` belongs to $(key[1]); $(mod) may add trait-bounded " *
                                                  "methods to it only where it already has an entry of that shape (rule 3)")
        end
        nargs = nva == 0 ? length(args) : -1
        # an entry of trait positions and ordinary arguments reaches the table of declared
        # implementations for `Compiled` values whose caller does not know their types (untyped.jl)
        tabled = nva == 0 && isempty(kws) && all(x -> x.kind in (:trait, :plain, :untyped), args) &&
                 any(x -> x.kind === :trait, args) &&
                 !any(w -> any(x -> x.kind === :plain && x.ann !== nothing && _uses(x.ann, _wherevar(w)), args), wheres)   # a holder binds no type variable
        eargs = Any[]
        stmts = Any[]
        callnames = Any[]
        for x in args
            nm = x.name
            if x.kind === :trait
                # `@nospecialize`: a typed caller inlines the entry, where `known_type` folds to `true`;
                # an untyped caller reaches the one entry compiled at `Any`, where it is `false` (§6.6)
                push!(eargs, :(@nospecialize($nm)))
                push!(callnames, nm)
            elseif x.kind in (:callable, :callables)
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
        haskw && push!(stmts, :($ntname = $kwname))
        newnames = Any[]
        for (i, x) in enumerate(args)
            if x.kind === :trait
                v = gensym(Symbol(x.name, :_view))
                # `known_type` in the entry's own body: in a helper called with an `Any`-typed value it would be
                # compiled for the value's type, where it folds to `true` (E-148)
                push!(stmts, :($v = $TraitWorld.enter($TraitWorld.EntryPos{typeof($fname),$i,$nargs}(), $(x.name),
                                                      Val($TraitWorld._known_type($(x.name))))))
                fb = haskw ? :($TraitWorld.kwfallback($ntname, $fname, $(callnames...))) : :($TraitWorld.fallback($fname, $(callnames...)))
                push!(stmts, :($v === $TraitWorld.NOTRAIT && return $fb))
                push!(newnames, v)
            elseif x.kind === :vararg_trait
                v = gensym(Symbol(x.name, :_views))
                push!(stmts, :($v = $TraitWorld.enter_each($TraitWorld.EntryPos{typeof($fname),$i,-1}(), $(x.name),
                                                           Val($TraitWorld._known_type($(x.name))))))
                fb = haskw ? :($TraitWorld.kwfallback($ntname, $fname, $(callnames...))) : :($TraitWorld.fallback($fname, $(callnames...)))
                push!(stmts, :($v === $TraitWorld.NOTRAIT && return $fb))
                push!(newnames, Expr(:..., v))
            elseif x.kind === :callable
                v = gensym(Symbol(x.name, :_fn))
                push!(stmts, :($v = $TraitWorld.enter_callable($(x.A), $(x.S), $(QuoteNode(x.M)), $(x.name),
                                                               Val($TraitWorld._known_type($(x.name))))))
                push!(newnames, v)
            elseif x.kind === :callables
                v = gensym(Symbol(x.name, :_fn))
                sigs = Expr(:tuple, [Expr(:tuple, A, S, QuoteNode(M)) for (A, S, M) in x.traits]...)
                push!(stmts, :($v = $TraitWorld.enter_callables($sigs, $(x.name), Val($TraitWorld._known_type($(x.name))))))
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
                push!(stmts, :($ntname = $TraitWorld.enter_kw($tl, $fname, $k, $ntname, $(QuoteNode(x.M)), Val($TraitWorld._known_type($ntname)))))
            else
                push!(stmts, :($ntname = $TraitWorld.enter_kw_callable($(x.A), $(x.S), $(QuoteNode(x.M)), $k, $ntname,
                                                                       Val($TraitWorld._known_type($ntname)))))
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
        push!(stmts, :(return $res isa $TraitWorld.LikeResult ? $TraitWorld._like_return($res, $us, $vs) : $res))
        kept = Any[w for w in wheres if any(x -> x.kind in (:plain, :vararg) && x.ann !== nothing && _uses(x.ann, _wherevar(w)), args)]
        # with keywords, the entry is its own keyword sorter: Julia's would be specialized on the named tuple of
        # the supplied keywords, where `known_type` always sees their types; taken unspecialized, as the
        # positional arguments are, a typed caller inlines it and an untyped one does not (traits reference §5.7)
        esig = haskw ? Expr(:call, :(Core.kwcall), :(@nospecialize($kwname::NamedTuple)), :(::typeof($fname)), eargs...) :
                       Expr(:call, fname, eargs...)
        isempty(kept) || (esig = Expr(:where, esig, kept...))
        if haskw
            psig = Expr(:call, fname, eargs...)
            isempty(kept) || (psig = Expr(:where, psig, kept...))
            push!(rest, Expr(:macrocall, GlobalRef(Base, Symbol("@inline")), LineNumberNode(0, :none),
                             Expr(:function, psig, Expr(:block, Expr(:meta, :facts_boundary),
                                                        :(return Core.kwcall(NamedTuple(), $fname, $(callnames...)))))))
        end
        # an ordinary method, inlined into a typed caller (keys-plan §6): there it runs at plain speed.
        # It is the boundary (rule 2): compiled in its caller's mode, while the worker it calls is
        # compiled by facts (`Expr(:meta, :facts_boundary)`, read by Julia's compiler)
        if tabled
            # where a trait argument's type is not known here: its builder from the position's table,
            # then one dynamic call to the entry's method specialized on the builders (one per key)
            tag = gensym(Symbol(:tw_untyped_, fname isa Symbol ? fname : :f))
            tpos = [i for (i, x) in enumerate(args) if x.kind === :trait]
            bsyms = [gensym(:b) for _ in tpos]
            known = foldl((a, b) -> :($a | $b), [:($TraitWorld._known_object($(args[i].name), $TraitWorld._known_type($(args[i].name)))) for i in tpos])
            served = foldl((a, b) -> :($a & $b), [:($TraitWorld._tabled($TraitWorld.EntryPos{typeof($fname),$i,$nargs}(), $(args[i].name))) for i in tpos])
            # the values the table compiles for: a `compiled_for`'s held value, or the value
            usyms = Dict(i => gensym(Symbol(args[i].name, :_u)) for i in tpos)
            unwrap = Any[:($(usyms[i]) = $TraitWorld._unconverted($(args[i].name))) for i in tpos]
            ucall = Any[haskey(usyms, i) ? usyms[i] : callnames[i] for i in eachindex(args)]
            wsym = gensym(:w)
            look = Any[:($wsym = Base.tls_world_age())]
            for (j, i) in enumerate(tpos)
                push!(look, :($(bsyms[j]) = $TraitWorld._ubuilder($TraitWorld.EntryPos{typeof($fname),$i,$nargs}(),
                                                                     $(Expr(:new, :($TraitWorld.XAny), usyms[i])), $wsym)))
            end
            found = foldl((a, b) -> :($a & $b), [:($(bsyms[j]) isa $TraitWorld.Builder) for j in eachindex(tpos)])
            if length(tpos) == 1
                # one trait position: through the pattern's pointer for the type (no second dispatch)
                i1 = tpos[1]
                esym = gensym(:e)
                nall = length(args)
                tblock = :(if !($known) && $served
                               $(unwrap...)
                               $wsym = Base.tls_world_age()
                               $esym = $TraitWorld._pentry($TraitWorld.EntryPos{typeof($fname),$i1,$nargs}(), $tag(),
                                                           $(Expr(:new, :($TraitWorld.XAny), usyms[i1])), $wsym, Val($nall))
                               if getfield($esym, :fp) != C_NULL
                                   return ccall(getfield($esym, :fp), Any, ($([:Any for _ in 0:nall]...),), getfield($esym, :fo), $(ucall...))
                               end
                           end)
            else
                holders = [Expr(:new, :($TraitWorld.XAny), haskey(usyms, i) ? usyms[i] : x.name) for (i, x) in enumerate(args)]
                tblock = :(if !($known) && $served
                               $(unwrap...)
                               $(look...)
                               $found && return Base.inferencebarrier($tag())($(bsyms...), $(holders...))   # a dispatch, on the builders' types
                           end)
            end
            pushfirst!(stmts, tblock)
            # the specialized method: the views from the builders' data, the worker's call as the entry's.
            # Every argument comes in a concrete holder (`XAny`): passed as `Any`, a call to this method
            # from code compiled by facts would be a run-time site (the pointer's wrapper is such code)
            cargs = Any[]
            cstmts = Any[]
            cnames = Any[]
            for (i, x) in enumerate(args)
                xa = gensym(:xa)
                push!(cargs, :($xa::$TraitWorld.XAny))
                if x.kind === :trait
                    v = gensym(Symbol(x.name, :_view))
                    push!(cstmts, :($(x.name) = getfield($xa, :x)))
                    j = findfirst(==(i), tpos)
                    push!(cstmts, :($v = $TraitWorld._build_any($(bsyms[j]), $xa)))
                    push!(cstmts, :($TraitWorld.keeps($TraitWorld.KeepOf{typeof($fname)}()) && ($v = $TraitWorld._with_object_any($v, $xa))))
                    push!(cnames, v)
                else
                    # an ordinary argument: as declared (an untyped one stays `Any`, as in plain Julia)
                    push!(cstmts, x.ann === nothing ? :($(x.name) = getfield($xa, :x)) : :($(x.name) = getfield($xa, :x)::$(x.ann)))
                    push!(cnames, x.name)
                end
            end
            cres = gensym(:res)
            # a frame of its own: a backtrace shows the worker at its bound, as from the entry's call
            push!(cstmts, :($cres = $TraitWorld.checked_call($fname, $(cnames...))))
            push!(cstmts, :(return $cres isa $TraitWorld.LikeResult ?
                            Base.inferencebarrier($TraitWorld._like_out)($cres, $us, $(Expr(:tuple, [cnames[i] for i in tpos]...))) : $cres))
            csig = Expr(:call, :(::$tag), [:($(bsyms[j])::$TraitWorld.Builder) for j in eachindex(tpos)]..., cargs...)
            push!(rest, :(struct $tag end))
            push!(rest, Expr(:macrocall, GlobalRef(Base, Symbol("@noinline")), LineNumberNode(0, :none),
                             Expr(:function, csig, Expr(:block, cstmts...))))
            push!(rest, :(isdefined(@__MODULE__, :__tw_untyped__) && push!(__tw_untyped__, ($fname, $nargs, $tag(), $(Tuple(tpos))))))
        end
        pushfirst!(stmts, Expr(:meta, :facts_boundary))
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
        push!(rest, :($TraitWorld._note_position(@__MODULE__, $fname, $i, $(x.kind === :vararg_trait ? -1 : nargs_w), $(QuoteNode(x.M)))))
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

"Define `attribute(EntryPos{typeof(f), pos, nargs})` in `mod` where a bound there declares one (`Compiled{X}`, `Dynamic{X}`)."
function _fix_attribute!(mod::Module, @nospecialize(f), pos::Int, nargs::Int)
    isdefined(mod, :__tw_attrs__) || return nothing
    a = get(mod.__tw_attrs__, (f, pos, nargs), nothing)
    a === nothing && return nothing
    P = EntryPos{typeof(f),pos,nargs}
    m = Base._which(Tuple{typeof(attribute),P}; raise = false)
    m !== nothing && Base.unwrap_unionall(m.method.sig).parameters[2] === P && Base.invokelatest(attribute, P()) === a && return nothing
    Core.eval(mod, :($TraitWorld.attribute(::$P) = $(QuoteNode(a))))
    return nothing
end

"Define `crossing(EntryPos{typeof(f), pos, nargs})` in `mod` as a constant, as `needed` (redefined only when it changes)."
function _fix_crossing!(mod::Module, @nospecialize(f), pos::Int, nargs::Int)
    P = EntryPos{typeof(f),pos,nargs}
    C = crossing_at(f, pos, nargs)
    m = Base._which(Tuple{typeof(crossing),P}; raise = false)
    if m !== nothing && Base.unwrap_unionall(m.method.sig).parameters[2] === P
        Base.invokelatest(crossing, P()) === C && return nothing
        m.method.module === mod || ccall(:jl_generating_output, Cint, ()) == 0 || return nothing
    elseif C === nothing
        return nothing                                  # the fallback computes `nothing` too, once per call site's compilation
    end
    Core.eval(mod, :($TraitWorld.crossing(::$P) = $C))
    return nothing
end

"""
A trait position of an entry, noted where its worker is defined. Once the module is
complete, `needed` is fixed for it; a definition after that (at the prompt) updates it.
"""
function _note_position(mod::Module, @nospecialize(f), pos::Int, nargs::Int, attr::Union{Nothing,Symbol} = nothing)
    isdefined(mod, :__tw_positions__) || return nothing
    k = (f, pos, nargs)
    any(x -> x[1] === f && x[2] == pos && x[3] == nargs, mod.__tw_positions__) || push!(mod.__tw_positions__, k)
    if attr !== nothing && isdefined(mod, :__tw_attrs__)
        old = get(mod.__tw_attrs__, k, nothing)
        old === nothing || old === attr || throw(TraitBoundError("`$f`, argument $pos: its methods declare different " *
                                                                 "attributes there, $old and $attr; declare one"))
        mod.__tw_attrs__[k] = attr
    end
    mod.__tw_finished__[] && (_fix_needed!(mod, f, pos, nargs); _fix_keeps!(mod, f))
    return nothing
end

"""
Define `needed(EntryPos{typeof(f), pos, nargs})` in `mod`: the traits the workers of `f` need
there, as a constant, so that an entry folds for a known type. Redefined only when they change.
"""
function _fix_needed!(mod::Module, @nospecialize(f), pos::Int, nargs::Int)
    P = EntryPos{typeof(f),pos,nargs}
    _fix_crossing!(mod, f, pos, nargs)
    _fix_attribute!(mod, f, pos, nargs)
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
    _warn_hidden_attributes(mod)
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
