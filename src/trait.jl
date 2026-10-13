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
    h isa Expr && h.head === :curly && length(h.args) == 2 && h.args[1] isa Symbol && h.args[2] isa Symbol ||
        error("@trait: expected `Name{R}`, got `$h`")
    return h.args[1]::Symbol, h.args[2]::Symbol, supers
end

macro trait(header, block = nothing)
    name, Rsym, supers = _parse_trait_header(header)
    TW = TraitWorld
    out = Any[:(Core.@__doc__ abstract type $name{$Rsym} <: $TW.Trait end)]
    if block === nothing
        isempty(supers) && error("@trait: `$name` has neither operations nor traits it bundles")
        push!(out, :($TW.bundle(::Type{$name}) = ($(supers...),)))
        push!(out, :($name))
        return esc(Expr(:block, out...))
    end
    block isa Expr && block.head === :block || error("@trait: expected a begin … end block")
    decls = _OpDecl[]
    for ex in block.args
        ex isa LineNumberNode && continue
        push!(decls, _parse_opdecl(ex, Rsym))
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
        argtypes = [t for (_, t) in d.args]
        first_decl && push!(out, :($TW.op_function(::Type{$name}, ::Val{$key}) = $(d.fexpr)))
        push!(out, :($TW.op_args(::Type{$name}, ::Val{$key}, ::Type{$Rsym}, ::Val{$N}) where {$Rsym} = Tuple{$(argtypes...)}))
        push!(out, :($TW.op_ret(::Type{$name}, ::Val{$key}, ::Type{$Rsym}, ::Val{$N}) where {$Rsym} = $(d.ret)))
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
        push!(out, :(@inline $(d.fexpr)(t::$TW.TObj{$T}, args...) where {$T >: $name} =
                         $TW.opcall($name, Val($key), $(d.fexpr), $TW.viewof(t, $name), args...)))
    end
    push!(out, :($name))
    return esc(Expr(:block, out...))
end
