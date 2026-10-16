# ---------------------------------------------------------------------------
# @trait: declare a trait over a representation parameter.
#
#     @trait ColTable{R} begin
#         ncols(r::R)::Int                                   # a new function, owned by this module
#         col(r::R, i::Int)::Vector{Float64}
#         firstcol(r::R)::Vector{Float64} = col(r, 1)         # a default
#     end
#     @trait Indexable{R} <: HasLength begin
#         Base.getindex(r::R, i::Int)::eltype(R)             # an existing function
#     end
#     @trait Table{R} <: (ColTable, RowTable)                # a bundle: t::Table means t::(ColTable, RowTable)
#     @mutating setcol!(r::R, i::Int, v::Vector{Float64})::Nothing   # inside a trait body
# ---------------------------------------------------------------------------

"Whether expression `ex` mentions the symbol `R`."
_mentions(ex, R::Symbol) = ex === R || (ex isa Expr && any(a -> _mentions(a, R), ex.args))

struct _OpDecl
    name::Symbol          # the operation's key
    fexpr::Any            # the function, as written (`ncols`, `Base.getindex`)
    rname::Symbol         # the name of the representation argument
    args::Vector{Any}     # (name, type expression) of the arguments after r
    ret::Any              # result type expression (may mention R)
    default::Any          # body of the default, or nothing
    mutating::Bool
end

_fname_key(f::Symbol) = f
_fname_key(f::Expr) = (f.head === :. && f.args[end] isa QuoteNode) ? f.args[end].value :
                      error("@trait: cannot use `$f` as an operation name")

function _parse_opdecl(ex, Rsym::Symbol)
    mutating = false
    if ex isa Expr && ex.head === :macrocall && ex.args[1] === Symbol("@mutating")
        mutating = true
        ex = ex.args[end]
    end
    default = nothing
    if ex isa Expr && ex.head === :(=)
        default = ex.args[2]
        ex = ex.args[1]
    end
    ex isa Expr && ex.head === :(::) && length(ex.args) == 2 ||
        error("@trait: declare each operation with its result type, as in `f(r::$Rsym, i::Int)::T`; got `$ex`")
    call, ret = ex.args
    call isa Expr && call.head === :call || error("@trait: expected a call, got `$call`")
    fexpr = call.args[1]
    length(call.args) >= 2 || error("@trait: `$fexpr` needs the representation as its first argument")
    first = call.args[2]
    first isa Expr && first.head === :(::) && length(first.args) == 2 && first.args[2] === Rsym ||
        error("@trait: the first argument of `$fexpr` must be `r::$Rsym`")
    rname = first.args[1]
    args = Any[]
    for a in call.args[3:end]
        if a isa Expr && a.head === :(::)
            push!(args, length(a.args) == 2 ? (a.args[1], a.args[2]) : (gensym(:x), a.args[1]))
        elseif a isa Symbol
            push!(args, (a, :Any))
        else
            error("@trait: unsupported argument `$a` in `$fexpr`")
        end
    end
    return _OpDecl(_fname_key(fexpr), fexpr, rname, args, ret, default, mutating)
end

function _parse_trait_header(h)
    supers = Any[]
    isbundle = false
    if h isa Expr && h.head === :(<:)
        s = h.args[2]
        if s isa Expr && s.head === :tuple
            append!(supers, s.args)
        else
            push!(supers, s)
        end
        h = h.args[1]
    end
    h isa Expr && h.head === :curly && length(h.args) >= 2 && h.args[1] isa Symbol && h.args[end] isa Symbol ||
        error("@trait: expected `Name{R}` or `Name{P…, R}`, the representation last; got `$h`")
    # parameters before the representation: associated types, optionally bounded (`T <: NumberLike`)
    params = Any[]
    for a in h.args[2:end-1]
        if a isa Symbol
            push!(params, (a, nothing))
        elseif a isa Expr && a.head === :(<:) && a.args[1] isa Symbol
            push!(params, (a.args[1], a.args[2]))
        else
            error("@trait: a parameter is a name, optionally bounded (`T <: NumberLike`); got `$a`")
        end
    end
    return h.args[1]::Symbol, h.args[end]::Symbol, supers, params
end

"""
The trait syntax of the design (note "Declaring a trait"): operations declared at the trait,
`ncols(t::ColTable)::Int`, `Self` for the implementing type, every header parameter an
associated type. Lowered to the internal form, whose last parameter is the implementing
type, named `Self`. A trait whose operations take `r::R`, `R` the header's last parameter,
is the earlier spelling and passes unchanged. Returns the header, the block, and the
(parameter, field) pairs where a field's type is a parameter.
"""
function _keys_form(header, block)
    h = header isa Expr && header.head === :(<:) ? header.args[1] : header
    name = h isa Symbol ? h : (h isa Expr && h.head === :curly ? h.args[1] : nothing)
    name isa Symbol || return header, block, Tuple{Symbol,Symbol}[]
    hps = h isa Symbol ? Any[] : h.args[2:end]
    pnames = Symbol[p isa Symbol ? p : p.args[1] for p in hps]
    ops = block === nothing ? Any[] : Any[_opcall(ex) for ex in block.args if _opcall(ex) !== nothing]
    firsttypes = Any[length(c.args) >= 2 && c.args[2] isa Expr && c.args[2].head === :(::) ? c.args[2].args[end] : nothing for c in ops]
    # the earlier spelling: the operations' first argument typed by the header's last parameter
    !isempty(pnames) && any(t -> t === pnames[end], firsttypes) && return header, block, Tuple{Symbol,Symbol}[]
    if block === nothing && h isa Symbol
        # a bundle, `@trait Table <: (ColTable, RowTable)`
        return (header isa Expr ? Expr(:(<:), Expr(:curly, name, :Self), header.args[2]) : Expr(:curly, name, :Self)), block, Tuple{Symbol,Symbol}[]
    end
    newh = Expr(:curly, name, hps..., :Self)
    newheader = header isa Expr && header.head === :(<:) ? Expr(:(<:), newh, header.args[2]) : newh
    block === nothing && return newheader, block, Tuple{Symbol,Symbol}[]
    fieldparams = Tuple{Symbol,Symbol}[]
    newblock = Expr(:block)
    for ex in block.args
        c = _opcall(ex)
        if c !== nothing
            push!(newblock.args, _self_first(ex, name))
            continue
        end
        fd = ex isa Expr && ex.head === :macrocall && ex.args[1] === Symbol("@const") ? ex.args[end] : ex
        if fd isa Expr && fd.head === :(::) && length(fd.args) == 2 && fd.args[1] isa Symbol && fd.args[2] isa Symbol && fd.args[2] in pnames
            push!(fieldparams, (fd.args[2], fd.args[1]))
        end
        push!(newblock.args, ex)
    end
    return newheader, newblock, fieldparams
end
"The call of an operation declaration (`f(t::X, …)::T`, a default, `@mutating`), or nothing for fields and equations."
function _opcall(ex)
    ex isa Expr && ex.head === :macrocall && ex.args[1] === Symbol("@mutating") && (ex = ex.args[end])
    ex isa Expr && ex.head === :(=) && (ex = ex.args[1])
    ex isa Expr && ex.head === :(::) && length(ex.args) == 2 && ex.args[1] isa Expr && ex.args[1].head === :call || return nothing
    return ex.args[1]
end
"An operation declared at the trait, `f(t::X, …)` or `f(t::X{T}, …)` or `f(t::Self, …)`: its first argument typed `Self`."
function _self_first(ex, name::Symbol)
    ex isa Expr && ex.head === :macrocall && return Expr(:macrocall, ex.args[1:end-1]..., _self_first(ex.args[end], name))
    ex isa Expr && ex.head in (:(=), :(::)) && return Expr(ex.head, _self_first(ex.args[1], name), ex.args[2:end]...)
    ex isa Expr && ex.head === :call || return ex
    first = length(ex.args) >= 2 ? ex.args[2] : nothing
    if first isa Expr && first.head === :(::)
        T = first.args[end]
        if T === name || T === :Self || (T isa Expr && T.head === :curly && T.args[1] === name)
            return Expr(:call, ex.args[1], Expr(:(::), (length(first.args) == 2 ? first.args[1] : gensym(:t)), :Self), ex.args[3:end]...)
        end
    end
    error("@trait: the first argument of `$(ex.args[1])` must be typed by the trait, `t::$name`")
end

"Replace the parameter names in a type expression by their values at the representation: `T` becomes `param(X, Val(:T), R)`."
function _subst_params(ex, pnames::Vector{Symbol}, name, Rsym::Symbol)
    TW = TraitWorld
    ex isa Symbol && ex in pnames && return :($TW.param($name, Val($(QuoteNode(ex))), $Rsym))
    ex isa Expr || return ex
    return Expr(ex.head, Any[_subst_params(a, pnames, name, Rsym) for a in ex.args]...)
end

"The `where` clause of a method on trait objects carrying trait `name`: a type variable per parameter and the representation."
function _tobj_where(name, np::Int, T::Symbol)
    vs = [gensym(:P) for _ in 1:np+1]
    return Any[vs..., Expr(:(>:), T, Expr(:curly, name, vs...))]
end

macro trait(header, block = nothing)
    header, block, fieldparams = _keys_form(header, block)
    name, Rsym, supers, params = _parse_trait_header(header)
    TW = TraitWorld
    pnames = Symbol[p for (p, _) in params]
    np = length(pnames)
    out = Any[:(Core.@__doc__ abstract type $name{$(pnames...), $Rsym} <: $TW.Trait end)]
    if np > 0
        push!(out, :($TW.trait_params(::Type{$name}) = $(Tuple(pnames))))
        for (i, (p, b)) in enumerate(params)
            key = QuoteNode(p)
            # at an archetype: the value a bound fixes, else an opaque stand-in
            push!(out, :($TW.param(::Type{$name}, ::Val{$key}, ::Type{A}) where {A <: $TW.Archetype} = $TW._archparam(A, $name, $key, $i)))
            b === nothing || push!(out, :($TW.param_bound(::Type{$name}, ::Val{$key}) = $b))
        end
    end
    if block === nothing
        isempty(supers) && error("@trait: `$name` has neither operations nor traits it bundles")
        push!(out, :($TW.bundle(::Type{$name}) = ($(supers...),)))
        push!(out, :($TW._bump!()))
        push!(out, :($name))
        return esc(Expr(:block, out...))
    end
    block isa Expr && block.head === :block || error("@trait: expected a begin … end block")
    decls = _OpDecl[]
    fdecls = Any[]                     # (name, type expression, writable)
    for ex in block.args
        ex isa LineNumberNode && continue
        if ex isa Expr && ex.head === :(=) && ex.args[1] isa Symbol && ex.args[1] in pnames
            # a defining equation: the parameter as a function of the representation (`T = eltype(R)`)
            push!(out, :($TW.param(::Type{$name}, ::Val{$(QuoteNode(ex.args[1]))}, ::Type{K__}) where {K__} =
                             (let $Rsym = $TW._impl(K__); $(ex.args[2]); end)))
        elseif ex isa Expr && ex.head === :(::) && length(ex.args) == 2 && ex.args[1] isa Symbol
            push!(fdecls, (ex.args[1], ex.args[2], true))          # a field, writable as in a mutable struct
        elseif ex isa Expr && ex.head === :macrocall && ex.args[1] === Symbol("@const") &&
               ex.args[end] isa Expr && ex.args[end].head === :(::) && ex.args[end].args[1] isa Symbol
            # `@const name::T`: a read-only field (`const name::T` parses only inside a struct)
            push!(fdecls, (ex.args[end].args[1], ex.args[end].args[2], false))
        else
            push!(decls, _parse_opdecl(ex, Rsym))
        end
    end
    length(unique(first.(fdecls))) == length(fdecls) || error("@trait: a field is declared twice in `$name`")
    # a parameter that types a field is that field's type (note "Declaring a trait": a field defines its type's parameter)
    for (p, f) in fieldparams
        any(ex -> ex isa Expr && ex.head === :(=) && ex.args[1] === p, block.args) &&
            error("@trait: parameter `$p` of `$name` is defined by the field `$f` and by an equation; define it once")
        push!(out, :($TW.param(::Type{$name}, ::Val{$(QuoteNode(p))}, ::Type{K__}) where {K__ <: $TW.Key} = $TW._keyfield(K__, $(QuoteNode(f)))))
    end
    sigs = [(d.name, length(d.args)) for d in decls]
    length(unique(sigs)) == length(sigs) || error("@trait: an operation is declared twice with the same arity in `$name`")
    names = unique([d.name for d in decls])
    isempty(supers) || push!(out, :($TW.supertraits(::Type{$name}) = ($(supers...),)))
    push!(out, :($TW.trait_ops(::Type{$name}) = $(Tuple(names))))
    done = Symbol[]
    for d in decls
        key = QuoteNode(d.name)
        first_decl = !(d.name in done)
        push!(done, d.name)
        if d.fexpr isa Symbol && first_decl
            push!(out, :(function $(d.fexpr) end))
        end
        N = length(d.args)
        argtypes = [_subst_params(t, pnames, name, :K__) for (_, t) in d.args]
        first_decl && push!(out, :($TW.op_function(::Type{$name}, ::Val{$key}) = $(d.fexpr)))
        push!(out, :($TW.op_args(::Type{$name}, ::Val{$key}, ::Type{K__}, ::Val{$N}) where {K__} =
                         (let $Rsym = $TW._impl(K__); Tuple{$(argtypes...)}; end)))
        push!(out, :($TW.op_ret(::Type{$name}, ::Val{$key}, ::Type{K__}, ::Val{$N}) where {K__} =
                         (let $Rsym = $TW._impl(K__); $(_subst_params(d.ret, pnames, name, :K__)); end)))
        d.mutating && push!(out, :($TW.is_mutating(::Type{$name}, ::Val{$key}) = true))
        if d.default !== nothing
            argnames = [n for (n, _) in d.args]
            any(e -> e.name === d.name && e.default !== nothing && e !== d, decls[1:findfirst(==(d), decls)-1]) ||
                push!(out, :($TW.has_default(::Type{$name}, ::Val{$key}) = true))
            push!(out, :($TW.op_default(::Type{$name}, ::Val{$key}, $(d.rname), $(argnames...)) = $(d.default)))
        end
        first_decl || continue
        # the operation on trait objects: the only methods library code can call on one
        T = gensym(:T)
        push!(out, Expr(:macrocall, Symbol("@inline"), LineNumberNode(0),
                        Expr(:(=), Expr(:where, :($(d.fexpr)(t::$TW.TObj{$T}, args...)), _tobj_where(name, np, T)...),
                             Expr(:block, :($TW.opcall($name, Val($key), $(d.fexpr), t, args...))))))
    end
    # the operations on a dynamic value: dispatch on the trait object it keeps, assert the
    # declared result type where it does not depend on the representation
    for d in decls
        syms = [gensym(:a) for _ in d.args]
        retx = (_mentions(d.ret, Rsym) || any(p -> _mentions(d.ret, p), pnames)) ? :Any : d.ret
        # a constructor operation (result R) gives a dynamic value of the same conformance
        call = :($(d.fexpr)($TW.opened(dyn), $(syms...)))
        rhs = d.ret === Rsym ? :($TW._dyn_like(dyn, $call)) : :($TW._dyn_assert($call, $retx))
        push!(out, :(@inline $(d.fexpr)(dyn::$TW.Dynamic{<:$name}, $(syms...)) = $rhs))
    end
    # fields: properties of the representation, or (type R) the projection, read through a lens when written
    if !isempty(fdecls)
        push!(out, :($TW.trait_fields(::Type{$name}) = $(Tuple((f, w) for (f, _, w) in fdecls))))
        for (f, Tex, w) in fdecls
            key = QuoteNode(f)
            T = gensym(:T)
            push!(out, :($TW.field_type(::Type{$name}, ::Val{$key}, ::Type{K__}) where {K__} =
                             (let $Rsym = $TW._impl(K__); $(_subst_params(Tex, pnames, name, :K__)); end)))
            push!(out, :($TW._fieldpos(::Type{$name}, ::Val{$key}) = $(findfirst(x -> x[1] === f, fdecls))))
            Tex === Rsym && push!(out, :($TW.field_isrep(::Type{$name}, ::Val{$key}) = true))
            push!(out, Expr(:(=), Expr(:where, :($TW._tgetprop(t::$TW.TObj{$T}, ::Val{$key})), _tobj_where(name, np, T)...),
                            :($TW.fieldget($name, Val($key), t))))
            push!(out, Expr(:(=), Expr(:where, :($TW._tsetprop!(t::$TW.TObj{$T}, ::Val{$key}, x)), _tobj_where(name, np, T)...),
                            w ? :($TW.fieldset!($name, Val($key), t, x)) : :($TW._readonly($name, $key))))
        end
    end
    push!(out, :($TW._bump!()))
    push!(out, :($name))
    return esc(Expr(:block, out...))
end
