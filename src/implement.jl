# ---------------------------------------------------------------------------
# @implement: implementations (per representation, per family, generic) and
# projections (single, joint, dynamic). All are registered as methods, so they
# are serialized with the package that defines them, and owned by it (rule 5).
#
#     @implement ColTable{Vector{Vector{Float64}}} begin ncols(r) = …; col(r, i) = … end
#     @implement Indexable{A} where {A <: AbstractVector}            # a family, Base's own methods
#     @implement ColTable{R} where {R: Indexable, eltype(R) == Vector{Float64}} begin … end   # generic
#     @implement ColTable Measurements project(t) = t.series          # a projection
#     @implement ColTable{Ramp} begin … end                          # a user type, its own representation
#     @implement ColTable Reversed dynamic begin project(t) = …; col(r, i) = … end
#     @implement (ColTable, RowTable) Both project(t) = t.data        # one projection for two traits
#     @implement Store Frozen copies project(t) = copy(t.data)        # a projection that copies
# ---------------------------------------------------------------------------

"How a representation implements a trait: by its own methods (`:methods`) or by Base's, for a family (`:family`)."
struct ImplRec
    kind::Symbol
    defaults::Tuple
end
"`implementation(X, R)`: an `ImplRec`, or `nothing`. Generic implementations are found separately."
implementation(@nospecialize(X), @nospecialize(R)) = nothing

"A generic implementation: constraint traits, a predicate on the representation, the operations left to defaults."
struct GenericRec
    constraints::Tuple
    pred::Any
    defaults::Tuple
end

"A projection: the function, its representation, whether it copies the user's data, and dynamic operations if any."
struct ProjRec
    project::Any
    R::Any
    copies::Bool
    dyn::Any
end
"`projection(X, T)`: a `ProjRec`, or `nothing`. A representation is its own projection."
projection(@nospecialize(X), @nospecialize(T)) = nothing

struct ImplementError <: Exception
    msg::String
end
Base.showerror(io::IO, e::ImplementError) = print(io, "ImplementError: ", e.msg)

"Recursive concreteness: `T`, its type parameters, and its field types, all the way down."
function deep_concrete(@nospecialize(T); seen = Base.IdSet{Any}())
    T isa Type || return true
    T in seen && return true
    push!(seen, T)
    isconcretetype(T) || return false
    if T isa DataType
        for p in T.parameters
            deep_concrete(p; seen) || return false
        end
    end
    for i in 1:fieldcount(T)
        deep_concrete(fieldtype(T, i); seen) || return false
    end
    return true
end

# --- lookups, all through invokelatest: the machinery takes no edges --------

_impl(@nospecialize(X), @nospecialize(R)) = Base.invokelatest(implementation, X, R)
_proj(@nospecialize(X), @nospecialize(T)) = Base.invokelatest(projection, X, T)
_supers(@nospecialize(X)) = Base.invokelatest(supertraits, X)::Tuple
_bundle(@nospecialize(X)) = Base.invokelatest(bundle, X)
_ops(@nospecialize(X)) = Base.invokelatest(trait_ops, X)::Tuple
_opfn(@nospecialize(X), op::Symbol) = Base.invokelatest(op_function, X, Val(op))
_hasdefault(@nospecialize(X), op::Symbol) = Base.invokelatest(has_default, X, Val(op))::Bool
_mutating(@nospecialize(X), op::Symbol) = Base.invokelatest(is_mutating, X, Val(op))::Bool

"Arities declared for an operation (the number of arguments after `r`)."
function _arities(@nospecialize(X), op::Symbol)
    out = Int[]
    for m in methods(op_args, Tuple{Type{X},Val{op},Any,Any})
        sig = Base.unwrap_unionall(m.sig)
        p = sig.parameters[end]
        p isa DataType && p <: Val && push!(out, p.parameters[1])
    end
    return sort!(out)
end
_declared_args(@nospecialize(X), op::Symbol, @nospecialize(R), N::Int) = Base.invokelatest(op_args, X, Val(op), R, Val(N))
_declared_ret(@nospecialize(X), op::Symbol, @nospecialize(R), N::Int) = Base.invokelatest(op_ret, X, Val(op), R, Val(N))

"A trait and its supertraits, transitively, the trait first."
function trait_closure(@nospecialize(X))
    out = Any[X]
    i = 1
    while i <= length(out)
        for S in _supers(out[i])
            any(x -> x === S, out) || push!(out, S)
        end
        i += 1
    end
    return out
end

"The traits a bound names: a bundle's traits, or the trait itself."
function bound_traits(@nospecialize(X))
    b = _bundle(X)
    b === nothing && return Any[X]
    out = Any[]
    for Y in b
        append!(out, bound_traits(Y))
    end
    return out
end

function _generic_keys(@nospecialize(X))
    out = Symbol[]
    for m in methods(generic_rec, Tuple{Type{X},Any})
        sig = Base.unwrap_unionall(m.sig)
        p = sig.parameters[end]
        p isa DataType && p <: Val && push!(out, p.parameters[1])
    end
    return out
end

# --- conformance --------------------------------------------------------------

"""
Check that the operations `ops` of `X` have methods at `R` whose inferred
results are the declared types. Returns a list of problems.
"""
function conformance_problems(@nospecialize(X), @nospecialize(R), ops)
    problems = String[]
    for op in ops
        f = _opfn(X, op)
        for N in _arities(X, op)
            A = _declared_args(X, op, R, N)
            D = _declared_ret(X, op, R, N)
            sig = Tuple{R,A.parameters...}
            if !all(isconcretetype, A.parameters)
                # an abstract declared argument (an iteration state, say): inference there says little,
                # so ask only that a method exists that does not always throw; every call asserts the result
                ms = Base._methods_by_ftype(Tuple{typeof(f),sig.parameters...}, -1, Base.get_world_counter())
                if !(ms isa Vector) || isempty(ms)
                    push!(problems, "`$op` has no method for $sig")
                end
                continue
            end
            if !hasmethod(f, sig)
                push!(problems, "`$op` has no method for $sig")
                continue
            end
            T = Base.infer_return_type(f, sig)
            if T === Union{}
                push!(problems, "`$op` at $sig always throws (inferred `Union{}`): a fallback, not an implementation")
            elseif !(T <: D)
                push!(problems, "`$op` at $sig returns `$T`, declared `$D`")
            end
        end
    end
    return problems
end

const _FAMILY_WARNED = Set{Tuple{Any,Any}}()

# --- witnesses -------------------------------------------------------------------

const _WITNESS = Dict{Tuple{Any,Any},Any}()
const _WITNESS_WORLD = Ref{UInt}(0)

function _flush_if_stale!(cache::Dict, worldref::Ref{UInt})
    w = Base.get_world_counter()
    if worldref[] != w
        empty!(cache)
        worldref[] = w
    end
    return nothing
end

"""
    witness(X, R)

How representation `R` implements trait `X`: `Impl{defaults}()`, or a
`Generic` with its constraint witnesses, or `nothing`.
"""
function witness(@nospecialize(X), @nospecialize(R))
    @lock _LOCK begin
        _flush_if_stale!(_WITNESS, _WITNESS_WORLD)
        key = (X, R)
        haskey(_WITNESS, key) && return _WITNESS[key]
        w = _witness(X, R)
        _WITNESS[key] = w
        return w
    end
end

"Whether `R` has a method of every declared arity of operation `op` (abstract declared arguments: some method)."
function _has_op_method(@nospecialize(X), op::Symbol, @nospecialize(R))
    f = _opfn(X, op)
    for N in _arities(X, op)
        A = _declared_args(X, op, R, N)
        sig = Tuple{typeof(f),R,A.parameters...}
        if all(isconcretetype, A.parameters)
            hasmethod(f, Tuple{sig.parameters[2:end]...}) || return false
        else
            ms = Base._methods_by_ftype(sig, -1, Base.get_world_counter())
            (ms isa Vector && !isempty(ms)) || return false
        end
    end
    return true
end

"For existing methods (a family, or `@implement X{R}` without a block): the operations `R` has no method for and the trait has a default for."
_existing_defaults(@nospecialize(X), @nospecialize(R)) =
    Tuple(op for op in _ops(X) if _hasdefault(X, op) && !_has_op_method(X, op, R))

function _witness(@nospecialize(X), @nospecialize(R))
    rec = _impl(X, R)
    if rec isa ImplRec
        rec.kind === :methods && return Impl{rec.defaults}()
        # existing methods: defaults per representation
        D = _existing_defaults(X, R)
        if rec.kind === :family && isconcretetype(R) && !((X, R) in _FAMILY_WARNED)
            push!(_FAMILY_WARNED, (X, R))
            ps = conformance_problems(X, R, Tuple(op for op in _ops(X) if !(op in D)))
            isempty(ps) || @warn "$R is declared $(X) through a family, but does not conform:\n  " * join(ps, "\n  ")
        end
        return Impl{D}()
    end
    found = Any[]
    for k in _generic_keys(X)
        g = Base.invokelatest(generic_rec, X, Val(k))::GenericRec
        subs = Any[]
        ok = true
        for C in g.constraints, Y in trait_closure(C)
            any(s -> s[1] === Y, subs) && continue
            wy = witness(Y, R)
            wy === nothing && (ok = false; break)
            push!(subs, (Y, wy))
        end
        ok || continue
        g.pred === nothing || Base.invokelatest(g.pred, R)::Bool || continue
        push!(found, (k, g, subs))
    end
    isempty(found) && return nothing
    length(found) > 1 && throw(ImplementError("$R matches $(length(found)) generic implementations of $X " *
                                              "($(join(first.(found), ", "))), none more specific: add a specific implementation"))
    k, g, subs = found[1]
    sub = Tuple(Wit{Y}(wy) for (Y, wy) in subs)
    w = Generic{X,k,typeof(sub),g.defaults}(sub)
    if isconcretetype(R) && !((X, R) in _FAMILY_WARNED)
        # a generic implementation's results are checked at each concrete representation, as a family's are
        push!(_FAMILY_WARNED, (X, R))
        ps = _generic_problems(X, k, g, sub, R)
        isempty(ps) || @warn "the generic implementation of $X does not conform at $R:\n  " * join(ps, "\n  ")
    end
    return w
end

function _generic_problems(@nospecialize(X), k::Symbol, g::GenericRec, sub::Tuple, @nospecialize(R))
    problems = String[]
    S = _subobj_type(sub, R)
    for op in _ops(X)
        op in g.defaults && continue
        for N in _arities(X, op)
            A = _declared_args(X, op, R, N)
            all(isconcretetype, A.parameters) || continue
            D = _declared_ret(X, op, R, N)
            T = Base.infer_return_type(generic_op, Tuple{Type{X},Val{k},Val{op},S,A.parameters...})
            if T === Union{}
                push!(problems, "`$op` always throws at $R (inferred `Union{}`)")
            elseif !(T <: D)
                push!(problems, "`$op` returns `$T` at $R, declared `$D`")
            end
        end
    end
    return problems
end
"The type of the trait object a generic implementation's body receives at `R`."
function _subobj_type(sub::Tuple, @nospecialize(R))
    Xs = Any[typeof(s).parameters[1] for s in sub]
    vs = Any[View{typeof(s).parameters[1],typeof(s.w),R} for s in sub]
    return TObj{Union{Xs...},Tuple{vs...}}
end

"The projection of `T` for `X`: an explicit one, or `T` itself if it is a representation of `X`."
function proj_lookup(@nospecialize(X), @nospecialize(T))
    p = _proj(X, T)
    p isa ProjRec && return p
    witness(X, T) === nothing && return nothing
    return ProjRec(identity, T, false, nothing)
end

const _PWITNESS = Dict{Tuple{Any,Any},Any}()
const _PWITNESS_WORLD = Ref{UInt}(0)

"The witness a projection gives trait `X`: the representation's, or a dynamic table in front of it."
function proj_witness(@nospecialize(X), @nospecialize(T), p::ProjRec)
    p.dyn === nothing && return witness(X, p.R)
    @lock _LOCK begin
        _flush_if_stale!(_PWITNESS, _PWITNESS_WORLD)
        get!(_PWITNESS, (X, T)) do
            _dyn_witness(X, p)
        end
    end
end

function _dyn_witness(@nospecialize(X), p::ProjRec)
    R = p.R
    names = Symbol[]
    vals = Any[]
    for (op, f) in pairs(p.dyn)
        Ns = _arities(X, op)
        length(Ns) == 1 || throw(ImplementError("dynamic operation `$op` of $X must have one arity"))
        N = Ns[1]
        A = Tuple{R,_declared_args(X, op, R, N).parameters...}
        S = _declared_ret(X, op, R, N)
        push!(names, op)
        push!(vals, Erased{A,S}(f))
    end
    table = NamedTuple{Tuple(names)}(Tuple(vals))
    missing_ops = [op for op in _ops(X) if !(op in names) && !_hasdefault(X, op)]
    isempty(missing_ops) || throw(ImplementError("the dynamic operations for $X lack $(missing_ops), which have no default"))
    D = Tuple(op for op in _ops(X) if !(op in names))
    return Dyn{typeof(table),D}(table)
end

# --- checks run when an implementation or projection is defined (rule 5, rule 4) -------

function _owns(definer, @nospecialize(T))
    o = sig_owners(T)
    return definer in o
end

"""
Rule 5, delegation: an owner delegates by declaring a package extension. The
extension is loaded whenever its triggers are, so a call that could use its
methods sees them only if every trigger is a package its methods mention.
"""
function _check_delegate(mod::Module, @nospecialize(types...))
    r = Base.moduleroot(mod)
    trigs = _extension_triggers(r)
    trigs === nothing && return nothing
    mentioned = Base.IdSet{Any}()
    for T in types
        for o in sig_owners(T)
            push!(mentioned, o)
        end
    end
    for name in trigs
        tm = _loaded_root(name)
        tm === nothing && continue
        owner(tm) in mentioned || throw(ImplementError(
            "the extension $r is triggered by $name, which its methods do not mention: whether a call sees them " *
            "would depend on whether $name happens to be loaded (rule 5: a delegate is triggered only by packages its methods mention)"))
    end
    return nothing
end

function _check_implementation(mod::Module, @nospecialize(X), @nospecialize(R), given::Tuple)
    _check_delegate(mod, X, R)
    definer = owner(mod)
    tmod = owner(parentmodule(X))
    (definer === tmod || (R isa Type && _owns(definer, R))) ||
        throw(ImplementError("$(mod) may not implement $X for $R: it owns neither the trait nor the representation (rule 5)"))
    # rule 5 for the methods themselves: an operation that is someone else's function (Base.size)
    # may be implemented for R only by an owner of the function or of R, never by the trait's owner alone
    for op in given
        f = _opfn(X, op)
        for m in methods(f)
            m.module === mod || continue
            owned_method(m) || throw(ImplementError(
                "$(mod) defines $(m) to implement $X, but owns neither `$(nameof(f))` nor the types in its signature: " *
                "that would change `$(nameof(f))` for everyone (rule 5). Declare the existing methods instead " *
                "(`@implement $X{…}` without a block), or let the owner of $(R) implement it."))
        end
    end
    isconcretetype(R) || return nothing          # families and generic implementations are checked per representation
    deep_concrete(R) || throw(ImplementError("$R is not deeply concrete, so it cannot be a representation"))
    ps = conformance_problems(X, R, given)
    isempty(ps) || throw(ImplementError("the implementation of $X for $R does not conform:\n  " * join(ps, "\n  ")))
    for S in trait_closure(X)[2:end]
        witness(S, R) === nothing &&
            throw(ImplementError("$R implements $X but not its supertrait $S"))
    end
    return nothing
end

function _check_projection(mod::Module, @nospecialize(X), @nospecialize(T))
    _check_delegate(mod, X, T)
    p = _proj(X, T)::ProjRec
    definer = owner(mod)
    (definer === owner(parentmodule(X)) || _owns(definer, T)) ||
        throw(ImplementError("$(mod) may not project $T onto $X: it owns neither (rule 5)"))
    R = p.R
    (R isa Type && deep_concrete(R)) ||
        throw(ImplementError("the projection of $T for $X returns $R, which is not deeply concrete"))
    for Y in trait_closure(X)
        w = Y === X ? proj_witness(X, T, p) : witness(Y, R)
        w === nothing && throw(ImplementError("the projection of $T for $X returns $R, which does not implement $Y"))
        if p.copies
            for op in _ops(Y)
                _mutating(Y, op) && throw(ImplementError(
                    "$Y has the mutating operation `$op`, so it accepts only projections that share the user's data; " *
                    "the projection of $T copies (rule 4)"))
            end
        end
    end
    return nothing
end

"The representation a projection returns: declared, or inferred (must be concrete)."
function _rep_of(@nospecialize(f), @nospecialize(T), @nospecialize(Rdecl))
    Rinf = Base.infer_return_type(f, Tuple{T})
    if Rdecl !== nothing
        Rinf <: Rdecl || throw(ImplementError("the projection of $T returns $Rinf, declared $Rdecl"))
        return Rdecl
    end
    isconcretetype(Rinf) || throw(ImplementError(
        "cannot infer a concrete representation for the projection of $T (got $Rinf): declare it, as in `@implement Trait{R} $T …`"))
    return Rinf
end

# --- the macro --------------------------------------------------------------------

function _defs(block)
    defs = Any[]
    block isa Expr && block.head === :block || error("@implement: expected a begin … end block")
    for ex in block.args
        ex isa LineNumberNode && continue
        ex isa Expr && (ex.head === :(=) || ex.head === :function) && ex.args[1] isa Expr && ex.args[1].head === :call ||
            error("@implement: expected method definitions, got `$ex`")
        push!(defs, ex)
    end
    return defs
end
_defname(d) = d.args[1].args[1]::Symbol

"Turn `name(r, i) = body` into a method of the operation's function at `R`, annotating unannotated arguments as declared."
function _op_method(mod::Module, @nospecialize(X), d, Rex; precheck::Bool = true)
    call = d.args[1]
    name = call.args[1]::Symbol
    op = name
    op in _ops(X) || error("@implement: `$op` is not an operation of $X")
    f = _opfn(X, op)
    N = length(call.args) - 2
    N in _arities(X, op) || error("@implement: `$op` of $X is not declared with $N argument(s) after r")
    args = Any[]
    r = call.args[2]
    rname = r isa Expr ? r.args[1] : r
    push!(args, :($rname::$Rex))
    for (i, a) in enumerate(call.args[3:end])
        if a isa Symbol
            # the declared type, if it does not mention R
            T = try _declared_args(X, op, Any, N).parameters[i] catch; Any end
            push!(args, T === Any ? a : :($a::$T))
        else
            push!(args, a)
        end
    end
    # rule 5 before anything is defined: someone else's function (Base.size) may get a method
    # only for a representation the defining package owns
    if precheck && owner(parentmodule(f)) !== owner(mod)
        Rv = _tryeval(mod, Rex)
        if !(Rv isa Type && owner(mod) in sig_owners(Rv))
            throw(ImplementError(
                "$(mod) may not implement `$op` of $X for $(Rex): `$(nameof(f))` belongs to $(parentmodule(f)), and $(mod) does not own " *
                "$(Rex), so the method would change `$(nameof(f))` for everyone (rule 5). Declare the existing methods instead " *
                "(`@implement $(nameof(X)){$(Rex)}` without a block), or let the owner of $(Rex) implement it."))
        end
    end
    fref = Expr(:., parentmodule(f), QuoteNode(nameof(f)))
    return Expr(d.head, Expr(:call, fref, args...), d.args[2])
end

function _missing_and_defaults(@nospecialize(X), given)
    defaults = Symbol[]
    for op in _ops(X)
        op in given && continue
        _hasdefault(X, op) || error("@implement: $X needs the operation `$op` (it has no default)")
        push!(defaults, op)
    end
    return Tuple(defaults)
end

_flag(x) = x isa Symbol && x in (:dynamic, :copies)

macro implement(args...)
    mod = __module__
    _note_extension!(mod, __source__.file)
    TW = TraitWorld
    isempty(args) && error("@implement: nothing to implement")
    head = args[1]
    rest = collect(args[2:end])
    # --- projections: @implement X T …, @implement (X, Y) T …, @implement X{R} T …
    if !isempty(rest) && !(rest[1] isa Expr && rest[1].head === :block)
        return _implement_projection(mod, head, rest)
    end
    block = isempty(rest) ? nothing : rest[1]
    # --- generic and family implementations: X{R} where {...}
    if head isa Expr && head.head === :where
        return _implement_where(mod, head, block)
    end
    head isa Expr && head.head === :curly && length(head.args) == 2 ||
        error("@implement: expected `Trait{R}`, `Trait{R} where {…}`, or `Trait T …`; got `$head`")
    X = Core.eval(mod, head.args[1])
    Rex = head.args[2]
    if block === nothing
        # the representation's existing methods implement the trait (Base's, or its owner's)
        rec = gensym(:implementation)
        return esc(quote
            const $rec = $TW.ImplRec(:existing, ())
            $TW.implementation(::Type{$X}, ::Type{$Rex}) = $rec
            $TW._check_implementation(@__MODULE__, $X, $Rex,
                Tuple(op for op in $TW._ops($X) if !(op in $TW._existing_defaults($X, $Rex))))
            $TW._bump!()
            nothing
        end)
    end
    defs = _defs(block)
    given = Tuple(unique(_defname.(defs)))
    defaults = _missing_and_defaults(X, given)
    out = Any[_op_method(mod, X, d, Rex) for d in defs]
    rec = gensym(:implementation)
    push!(out, :(const $rec = $TW.ImplRec(:methods, $defaults)))
    push!(out, :($TW.implementation(::Type{$X}, ::Type{$Rex}) = $rec))
    push!(out, :($TW._check_implementation(@__MODULE__, $X, $Rex, $given)))
    push!(out, :($TW._bump!()))
    push!(out, :nothing)
    return esc(Expr(:block, out...))
end

function _implement_where(mod::Module, head, block)
    TW = TraitWorld
    tr = head.args[1]
    tr isa Expr && tr.head === :curly && length(tr.args) == 2 && tr.args[2] isa Symbol ||
        error("@implement: expected `Trait{R} where {…}`")
    X = Core.eval(mod, tr.args[1])
    Rsym = tr.args[2]::Symbol
    conds = head.args[2:end]
    constraints = Any[]
    preds = Any[]
    family = Any[]
    for c in conds
        if c isa Expr && c.head === :call && c.args[1] === :(:) && c.args[2] === Rsym
            push!(constraints, c.args[3])
        elseif c isa Expr && c.head === :(<:) && c.args[1] === Rsym
            push!(family, c)
        else
            push!(preds, c)
        end
    end
    if isempty(constraints) && isempty(preds)
        # a family: Base's (or the owner's) existing methods, or methods written for the whole family
        out = Any[]
        rec = gensym(:implementation)
        if block === nothing
            push!(out, :(const $rec = $TW.ImplRec(:family, ())))
            push!(out, :($TW.implementation(::Type{$X}, ::Type{$Rsym}) where {$(family...)} = $rec))
        else
            defs = _defs(block)
            given = Tuple(unique(_defname.(defs)))
            defaults = _missing_and_defaults(X, given)
            for d in defs
                m = _op_method(mod, X, d, Rsym)
                push!(out, Expr(m.head, Expr(:where, m.args[1], family...), m.args[2]))
            end
            push!(out, :(const $rec = $TW.ImplRec(:methods, $defaults)))
            push!(out, :($TW.implementation(::Type{$X}, ::Type{$Rsym}) where {$(family...)} = $rec))
        end
        famR = isempty(family) ? X : family[1].args[2]
        push!(out, :($TW._check_implementation(@__MODULE__, $X, $famR, ())))
        push!(out, :($TW._bump!()))
        push!(out, :nothing)
        return esc(Expr(:block, out...))
    end
    # a generic implementation over other traits
    block === nothing && error("@implement: a generic implementation needs a begin … end block")
    k = QuoteNode(gensym(Symbol(nameof(X), :_generic)))
    defs = _defs(block)
    given = Tuple(unique(_defname.(defs)))
    defaults = _missing_and_defaults(X, given)
    pred = if isempty(preds) && isempty(family)
        nothing
    else
        body = foldl((a, b) -> :($a && $b), [preds; [:($(f.args[1]) <: $(f.args[2])) for f in family]])
        :($Rsym -> $body)
    end
    out = Any[:($TW.generic_rec(::Type{$X}, ::Val{$k}) = $TW.GenericRec(($(constraints...),), $pred, $defaults))]
    for d in defs
        call = d.args[1]
        op = call.args[1]::Symbol
        op in _ops(X) || error("@implement: `$op` is not an operation of $X")
        push!(out, Expr(d.head, Expr(:call, :($TW.generic_op), :(::Type{$X}), :(::Val{$k}), :(::Val{$(QuoteNode(op))}),
                                     call.args[2:end]...), d.args[2]))
    end
    push!(out, :($TW._check_implementation(@__MODULE__, $X, $X, ())))
    push!(out, :($TW._bump!()))
    push!(out, :nothing)
    return esc(Expr(:block, out...))
end

function _implement_projection(mod::Module, head, rest)
    TW = TraitWorld
    traits = Any[]
    Rdecl = nothing
    if head isa Expr && head.head === :tuple
        append!(traits, head.args)
    elseif head isa Expr && head.head === :curly
        push!(traits, head.args[1])
        Rdecl = head.args[2]
    else
        push!(traits, head)
    end
    Tex = popfirst!(rest)
    flags = Symbol[]
    while !isempty(rest) && _flag(rest[1])
        push!(flags, popfirst!(rest))
    end
    length(rest) == 1 || error("@implement: expected `project(t) = …` or a begin … end block after the type")
    body = rest[1]
    dynamic = :dynamic in flags
    copies = :copies in flags
    defs = body isa Expr && body.head === :block ? _defs(body) : Any[body]
    pdefs = filter(d -> d isa Expr && d.args[1] isa Expr && d.args[1].args[1] === :project, defs)
    length(pdefs) == 1 || error("@implement: a projection needs exactly one `project(t) = …`")
    pdef = pdefs[1]
    ops = filter(d -> d !== pdef, defs)
    pcall = pdef.args[1]
    length(pcall.args) == 2 || error("@implement: `project` takes the value only")
    targ = pcall.args[2]
    tname = targ isa Expr ? targ.args[1] : targ
    pfn = gensym(:project)
    rec = gensym(:projection)
    Rconst = gensym(:R)
    out = Any[]
    push!(out, Expr(:function, Expr(:call, pfn, :($tname::$Tex)), pdef.args[2]))
    push!(out, :(const $Rconst = $TW._rep_of($pfn, $Tex, $(Rdecl === nothing ? nothing : Rdecl))))
    dynex = :nothing
    if !isempty(ops)
        length(traits) == 1 || error("@implement: operations come with a projection for one trait")
        X = Core.eval(mod, traits[1])
        if dynamic
            fields = Any[]
            for d in ops
                call = d.args[1]
                op = call.args[1]::Symbol
                op in _ops(X) || error("@implement: `$op` is not an operation of $X")
                fn = gensym(op)
                push!(out, Expr(d.head, Expr(:call, fn, call.args[2:end]...), d.args[2]))
                push!(fields, Expr(:(=), op, fn))
            end
            dynex = Expr(:tuple, Expr(:parameters, fields...))
        else
            # operations for the representation the projection returns: an implementation at R
            given = Tuple(unique(_defname.(ops)))
            defaults = _missing_and_defaults(X, given)
            for d in ops
                # R is known only once the projection is inferred: the methods are checked after definition
                push!(out, _op_method(mod, X, d, Rconst; precheck = false))
            end
            irec = gensym(:implementation)
            push!(out, :(const $irec = $TW.ImplRec(:methods, $defaults)))
            push!(out, :($TW.implementation(::Type{$(traits[1])}, ::Type{$Rconst}) = $irec))
            push!(out, :($TW._check_implementation(@__MODULE__, $(traits[1]), $Rconst, $given)))
        end
    elseif dynamic
        error("@implement: `dynamic` needs operations in the block")
    end
    push!(out, :(const $rec = $TW.ProjRec($pfn, $Rconst, $copies, $dynex)))
    for X in traits
        push!(out, :($TW.projection(::Type{$X}, ::Type{$Tex}) = $rec))
    end
    for X in traits
        push!(out, :($TW._check_projection(@__MODULE__, $X, $Tex)))
    end
    push!(out, :($TW._bump!()))
    push!(out, :nothing)
    return esc(Expr(:block, out...))
end
