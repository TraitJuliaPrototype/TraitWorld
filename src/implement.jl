# `@implement` and the implementation checks are cold code that works on expressions and types held
# as `Any`: its methods do not specialize on their arguments (`@nospecialize` for the whole file,
# undone at its end). Under the facts policy a call of one of them at abstract argument types is
# then a fact at a non-public function and compiles to an `:invoke` of the policy's code, instead
# of a run-time call into native code that large loads invalidate (session 26).
@nospecialize

# ---------------------------------------------------------------------------
# @implement: implementations (per representation, per family, generic) and
# projections (single, joint, dynamic). All are registered as methods, so they
# are serialized with the package that defines them, and owned by it (rule 3).
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
Base.Experimental.@max_methods 1 function implementation end
"`implementation(X, R)`: an `ImplRec`, or `nothing`. Generic implementations are found separately."
implementation(@nospecialize(X), @nospecialize(R)) = nothing

"A generic implementation: constraint traits, a predicate on the representation, the operations left to defaults."
struct GenericRec
    constraints::Tuple
    pred::Any
    defaults::Tuple
end

"""
An implementation (note "How a type conforms to a trait"): the receiver type `R`, the
forwarding field (`field`, or 0 when the type implements the operations itself), a
type's own operations called indirectly (`dyn`) if any, and the mapping of declared
fields to stored fields (`fmap`, `nothing` for the same names).
"""
struct ProjRec
    project::Any
    R::Any
    copies::Bool
    dyn::Any
    field::Int
    inverse::Any
    fmap::Any
end
ProjRec(project, R, copies::Bool, dyn) = ProjRec(project, R, copies, dyn, 0, nothing, nothing)
ProjRec(project, R, copies::Bool, dyn, field::Int) = ProjRec(project, R, copies, dyn, field, nothing, nothing)
ProjRec(project, R, copies::Bool, dyn, field::Int, inverse) = ProjRec(project, R, copies, dyn, field, inverse, nothing)
Base.Experimental.@max_methods 1 function projection end
"`projection(X, T)`: a `ProjRec`, or `nothing`. A representation is its own projection."
projection(@nospecialize(X), @nospecialize(T)) = nothing

struct ImplementError <: Exception
    msg::String
end
Base.showerror(io::IO, e::ImplementError) = print(io, "ImplementError: ", e.msg)

"""
A key part is concrete (decision 1, session 27): the type is concrete and its type parameters are,
all the way down. Fields the trait does not declare are not looked at: the code compiled for a key
never reads them. `Dynamic` and `Erased` parts are what they are.
"""
function key_concrete(@nospecialize(T))
    T isa Type || return true
    T === Union{} && return true
    isconcretetype(T) || return false
    (T <: Dynamic || T <: Erased) && return true
    if T isa DataType
        for p in T.parameters
            key_concrete(p) || return false
        end
    end
    return true
end
"The strictest concreteness policy of `X` and its supertraits."
function _concreteness_of(@nospecialize(X))
    pol = :none
    for Y in trait_closure(_family(X))
        p = _in_decision_world(trait_concreteness, Y)::Symbol
        p === :concrete_only && return p
        p === :warn && (pol = :warn)
    end
    return pol
end
"Apply `X`'s policy to a key part `T` (`what` names it in the message)."
function _concreteness_check(@nospecialize(X), @nospecialize(T), what::String)
    pol = _concreteness_of(X)
    pol === :none && return nothing
    key_concrete(T) && return nothing
    msg = "$what `$T` is not concrete, and $X asks for concrete keys"
    pol === :concrete_only && throw(ImplementError(msg * " (`@concrete_only`)"))
    @warn msg * " (`@warn_on_abstract`): code compiled for this key dispatches at run time where it reads that part"
    return nothing
end

"Recursive concreteness: `T`, its type parameters, and its field types, all the way down (used by concrete mode's reports)."
function deep_concrete(@nospecialize(T); seen = Base.IdSet{Any}())
    T isa Type || return true
    T in seen && return true
    push!(seen, T)
    isconcretetype(T) || return false
    # the design's dynamic positions: their `Any` field is what they are (note "Dynamic values", "Callable")
    (T <: Dynamic || T <: Erased) && return true
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

# --- lookups, in the decision world (`_in_decision_world`; the latest outside a decision) --------

_impl(@nospecialize(X), @nospecialize(R)) = _in_decision_world(implementation, X, R)
_proj(@nospecialize(X), @nospecialize(T)) = _in_decision_world(projection, X, T)
_supers(@nospecialize(X)) = _in_decision_world(supertraits, X)::Tuple
_bundle(@nospecialize(X)) = _in_decision_world(bundle, X)
_ops(@nospecialize(X)) = _in_decision_world(trait_ops, X)::Tuple
_opfn(@nospecialize(X), op::Symbol) = _in_decision_world(op_function, X, Val(op))
_hasdefault(@nospecialize(X), op::Symbol) = _in_decision_world(has_default, X, Val(op))::Bool
_mutating(@nospecialize(X), op::Symbol) = _in_decision_world(is_mutating, X, Val(op))::Bool

"""
The operations of `X` that `T` must implement (no default), one line each: the declared signature at
`T` and what `T` has of it, for an implementation error that says what is required.
"""
function _required_ops_text(@nospecialize(X), @nospecialize(T))
    lines = String[]
    for op in _ops(X)
        _hasdefault(X, op) && continue
        f = try Base.invokelatest(op_function, X, Val(op)) catch; nothing end
        Ns = _arities(X, op)
        isempty(Ns) && (Ns = _arities(_family(X), op))
        for N in Ns
            A = R = nothing
            for Y in (X, _family(X))
                A === nothing || break
                A = try Base.invokelatest(op_args, Y, Val(op), T, Val(N)) catch; nothing end
                R = try Base.invokelatest(op_ret, Y, Val(op), T, Val(N)) catch; nothing end
            end
            sig = "$op(::$T" * (A isa DataType ? join(", ::$a" for a in A.parameters) : ", …") * ")" * (R === nothing ? "" : "::$R")
            have = String[]
            if f isa Function
                for m in methods(f)
                    ps = Base.unwrap_unionall(m.sig).parameters
                    length(ps) >= 2 && typeintersect(T, ps[2]) !== Union{} && ps[2] !== Any && push!(have, string(m))
                end
            end
            push!(lines, "`$sig`: " * (isempty(have) ? "no method" : "not at the declared argument types; existing: " * join(first(have, 3), "; ")))
        end
    end
    return join(lines, "\n  ")
end

"Arities declared for an operation (the number of arguments after `r`)."
function _arities(@nospecialize(X), op::Symbol)
    out = Int[]
    for m in methods(op_args, Tuple{Type{X},Val{op},Any,Any})
        sig = Base.unwrap_unionall(m.sig)
        sig isa DataType || continue
        p = (sig.parameters::Core.SimpleVector)[end]
        p isa DataType && p <: Val && push!(out, p.parameters[1]::Int)
    end
    return sort!(out)
end
"All parameters concrete, by a loop (`all(isconcretetype, sv)` on a `SimpleVector` is generic Base code)."
_allconcrete(sv::Core.SimpleVector) = (for p in sv; (p isa Type && isconcretetype(p)) || return false; end; true)
_declared_args(@nospecialize(X), op::Symbol, @nospecialize(R), N::Int) = _in_decision_world(op_args, X, Val(op), R, Val(N))
_declared_ret(@nospecialize(X), op::Symbol, @nospecialize(R), N::Int) = _in_decision_world(op_ret, X, Val(op), R, Val(N))

"A trait and its supertraits, transitively, the trait first."
function trait_closure(@nospecialize(X))
    out = Any[X]
    i = 1
    while i <= length(out)
        for S in _supers(out[i])
            _hasid(out, S) || push!(out, S)
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
        sig isa DataType || continue
        p = (sig.parameters::Core.SimpleVector)[end]
        p isa DataType && p <: Val && push!(out, p.parameters[1]::Symbol)
    end
    return out
end

# --- the implementation check ---------------------------------------------------

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
            if !_allconcrete(A.parameters)
                # an abstract declared argument (an iteration state, say): inference there says little,
                # so ask only that a method exists that does not always throw; every call asserts the result
                ms = Base._methods_by_ftype(Tuple{typeof(f),sig.parameters...}, -1, _decision_world())
                if !(ms isa Vector) || isempty(ms)
                    push!(problems, "`$op` has no method for $sig")
                end
                continue
            end
            if !hasmethod(f, sig; world = _decision_world())       # the latest world: a check may run in an older one
                push!(problems, "`$op` has no method for $sig")
                continue
            end
            T = Base.infer_return_type(f, sig; _check_kw()...)
            if T === Union{}
                push!(problems, "`$op` at $sig always throws (inferred `Union{}`): a fallback, not an implementation")
            elseif !(T <: D)
                push!(problems, "`$op` at $sig returns `$T`, declared `$D`")
            end
        end
    end
    return problems
end

# keyed by Pair{Any,Any}: one specialization of the dictionary code, held in this image (a tuple key
# would compile `haskey` per pair of key types, at a new trait's first call)
const _FAMILY_WARNED = Set{Pair{Any,Any}}()

# --- witnesses -------------------------------------------------------------------

const _WITNESS = Dict{Pair{Any,Any},Any}()
const _WITNESS_WORLD = Ref{UInt}(0)

function _flush_if_stale!(cache::Dict, worldref::Ref{UInt})
    w = _decision_world()
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
        key = Pair{Any,Any}(X, R)
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
        if _allconcrete(A.parameters)
            hasmethod(f, Tuple{R,A.parameters...}; world = _decision_world()) || return false
        else
            ms = Base._methods_by_ftype(sig, -1, _decision_world())
            (ms isa Vector && !isempty(ms)) || return false
        end
    end
    return true
end

"For existing methods (a family, or `@implement X{R}` without a block): the operations `R` has no method for and the trait has a default for."
_existing_defaults(@nospecialize(X), @nospecialize(R)) =
    Tuple(op for op in _ops(X) if _hasdefault(X, op) && !_has_op_method(X, op, R))

# behind an inference barrier: `first.(found)` over a `Vector{Any}` gave the
# builder's code an edge to `first(::Any)`, which DataStructures extends, so
# loading CSV before TraitWorld invalidated every builder at load (view caches, x12)
@noinline function _ambiguous_generic(@nospecialize(X), @nospecialize(R), found::Vector{Any})
    throw(ImplementError("$R matches $(length(found)) generic implementations of $X " *
                         "($(join(first.(found), ", "))), none more specific: add a specific implementation"))
end

function _witness(@nospecialize(X), @nospecialize(R))
    # a trait without operations (only fields) is implemented by every representation; its fields are checked at the implementation
    isempty(_ops(X)) && isempty(_generic_keys(X)) && return Impl{()}()
    rec = _impl(X, R)
    if rec isa ImplRec
        rec.kind === :methods && return Impl{rec.defaults}()
        # existing methods: defaults per representation
        D = _existing_defaults(X, R)
        if rec.kind === :family && isconcretetype(R) && !(Pair{Any,Any}(X, R) in _FAMILY_WARNED)
            push!(_FAMILY_WARNED, Pair{Any,Any}(X, R))
            ps = conformance_problems(X, R, Tuple(op for op in _ops(X) if !(op in D)))
            isempty(ps) || @warn "$R is declared $(X) through a family, but does not conform:\n  " * join(ps, "\n  ")
        end
        return Impl{D}()
    end
    found = Any[]
    for k in _generic_keys(X)
        g = _in_decision_world(generic_rec, X, Val(k))::GenericRec
        subs = Any[]
        ok = true
        for C in g.constraints, Y in trait_closure(C)
            _hasfirst(subs, Y) && continue
            wy = witness(Y, R)
            wy === nothing && (ok = false; break)
            push!(subs, (Y, wy))
        end
        ok || continue
        g.pred === nothing || _in_decision_world(g.pred, R)::Bool || continue
        push!(found, (k, g, subs))
    end
    isempty(found) && return nothing
    length(found) > 1 && Base.inferencebarrier(_ambiguous_generic)(X, R, found)
    k, g, subs = found[1]
    sub = Tuple(Wit{_instance(Y, R)}(wy) for (Y, wy) in subs)
    w = Generic{X,k,typeof(sub),g.defaults}(sub)
    if isconcretetype(R) && !(Pair{Any,Any}(X, R) in _FAMILY_WARNED)
        # a generic implementation's results are checked at each concrete representation, as a family's are
        push!(_FAMILY_WARNED, Pair{Any,Any}(X, R))
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
            T = Base.infer_return_type(generic_op, Tuple{Type{X},Val{k},Val{op},S,A.parameters...}; _check_kw()...)
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
    vs = Any[_selfview_type(typeof(s).parameters[1], typeof(s.w), R) for s in sub]
    return TObj{_encode_traits(Xs),Tuple{vs...}}
end

_hasfirst(v::Vector{Any}, @nospecialize(y)) = (for s in v; (s::Tuple)[1] === y && return true; end; false)

"""
The implementation of `X` for `T`: a declared one, or `T` itself when it implements `X` and has
the fields `X` and its supertraits declare, under their own names. A type that implements
the operations but lacks the fields is a receiver type, not a member.
"""
function proj_lookup(@nospecialize(X), @nospecialize(T))
    p = _proj(X, T)
    p isa ProjRec && return p
    witness(X, T) === nothing && return nothing
    # a trait with fields: membership is declared per type, never conferred by a generic implementation
    any(Y -> !isempty(trait_fields(Y)), trait_closure(X)) && implementation(X, T) === nothing && return nothing
    for Y in trait_closure(X)
        isempty(_field_problems(Y, T, nothing, T)) || return nothing
    end
    return ProjRec(identity, T, false, nothing)
end

const _PWITNESS = Dict{Pair{Any,Any},Any}()
const _PWITNESS_WORLD = Ref{UInt}(0)

"The witness a projection gives trait `X`: the representation's, or a dynamic table in front of it."
function proj_witness(@nospecialize(X), @nospecialize(T), p::ProjRec)
    p.dyn === nothing && return witness(X, p.R)
    @lock _LOCK begin
        _flush_if_stale!(_PWITNESS, _PWITNESS_WORLD)
        get!(_PWITNESS, Pair{Any,Any}(X, T)) do
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

# --- checks run when an implementation or projection is defined (rule 3, rule 2) -------

function _owns(definer, @nospecialize(T))
    o = sig_owners(T)
    return definer in o
end

"""
Rule 3, delegation: an owner delegates by declaring a package extension. The
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
            "would depend on whether $name happens to be loaded (rule 3: a delegate is triggered only by packages its methods mention)"))
    end
    return nothing
end

_check_implementation(mod::Module, @nospecialize(X), @nospecialize(R), given::Tuple) =
    _latest(_check_implementation_now, mod, X, R, given)
@machinery function _check_implementation_now(mod::Module, @nospecialize(X), @nospecialize(R), given::Tuple)
    _check_delegate(mod, X, R)
    definer = owner(mod)
    tmod = owner(parentmodule(X))
    (definer === tmod || (R isa Type && _owns(definer, R))) ||
        throw(ImplementError("$(mod) may not implement $X for $R: it owns neither the trait nor the representation (rule 3)"))
    # rule 3 for the methods themselves: an operation that is someone else's function (Base.size)
    # may be implemented for R only by an owner of the function or of R, never by the trait's owner alone
    for op in given
        f = _opfn(X, op)
        for m in methods(f)
            m.module === mod || continue
            owned_method(m) || throw(ImplementError(
                "$(mod) defines $(m) to implement $X, but owns neither `$(nameof(f))` nor the types in its signature: " *
                "that would change `$(nameof(f))` for everyone (rule 3). Declare the existing methods instead " *
                "(`@implement $X{…}` without a block), or let the owner of $(R) implement it."))
        end
    end
    isconcretetype(R) || return nothing          # families and generic implementations are checked per type
    _concreteness_check(X, R, "the receiver type")
    ps = conformance_problems(X, R, given)       # the operations only: declared fields are checked with the declaration
    isempty(ps) || throw(ImplementError("the implementation of $X for $R does not conform:\n  " * join(ps, "\n  ")))
    for S in trait_closure(X)[2:end]
        witness(S, R) === nothing &&
            throw(ImplementError("$R implements $X but not its supertrait $S"))
    end
    return nothing
end

_check_projection(mod::Module, @nospecialize(X), @nospecialize(T)) = _latest(_check_projection_now, mod, X, T)
@machinery function _check_projection_now(mod::Module, @nospecialize(X), @nospecialize(T))
    _check_delegate(mod, X, T)
    p = _proj(X, T)::ProjRec
    definer = owner(mod)
    (definer === owner(parentmodule(X)) || _owns(definer, T)) ||
        throw(ImplementError("$(mod) may not declare that $T conforms to $X: it owns neither (rule 3)"))
    R = p.R
    R isa Type || throw(ImplementError("$T forwards $X to something that is not a type: $R"))
    R === Nothing || _concreteness_check(X, R, "$T forwards $X to a field whose type")
    for Y in trait_closure(X)
        w = Y === X ? proj_witness(X, T, p) : witness(Y, R)
        w === nothing && throw(ImplementError("$T forwards $X to a field of type $R, which does not implement $Y"))
        ps = _field_problems(Y, T, p.fmap, R)
        isempty(ps) || throw(ImplementError("$T does not have the fields $Y declares:\n  " * join(ps, "\n  ")))
    end
    return nothing
end

"A type declared to conform by its own methods has the fields the trait and its supertraits declare."
_check_own_fields(@nospecialize(X), @nospecialize(T)) = _latest(_check_own_fields_now, X, T)
@machinery function _check_own_fields_now(@nospecialize(X), @nospecialize(T))
    for Y in trait_closure(X)
        ps = _field_problems(Y, T, nothing, isempty(_ops(Y)) ? Nothing : T)
        isempty(ps) || throw(ImplementError("$T does not have the fields $Y declares:\n  " * join(ps, "\n  ")))
    end
    return nothing
end

"""
Problems of user type `T` with the fields trait `X` declares, mapped by `fmap` (else by
name): a stored field of the declared type, exactly that type and writable where the trait
writes it. A type with a `getproperty` of its own maps every field explicitly, because a
declared field is read with `getfield` and plain `x.name` may differ.
"""
function _field_problems(@nospecialize(X), @nospecialize(T), fmap, @nospecialize(R))
    ps = String[]
    isempty(trait_fields(X)) && return ps
    T isa DataType || return ["$T is not a concrete type with fields"]
    own_gp = which(getproperty, Tuple{T,Symbol}).sig.parameters[2] !== Any
    # the key with every declared field: a field's declared type may use a parameter another field defines
    fnames = Symbol[]; ftypes = Any[]
    for (f, _) in trait_fields(X)
        g = fmap === nothing ? f : get(fmap, f, f)
        hasfield(T, g) || continue
        push!(fnames, f); push!(ftypes, fieldtype(T, g))
    end
    Kfull = Key{isempty(_ops(X)) ? Nothing : R,NamedTuple{Tuple(fnames),Tuple{ftypes...}}}
    for (f, w) in trait_fields(X)
        g = fmap === nothing ? f : get(fmap, f, f)
        if own_gp && (fmap === nothing || !haskey(fmap, f))
            push!(ps, "$T defines its own `getproperty`, so field `$f` of $X must be mapped explicitly (`$f => storedfield`); " *
                      "it is read with `getfield`, and plain `x.$f` may differ")
            continue
        end
        if !hasfield(T, g)
            push!(ps, "$T has no field `$g`" * (g === f ? ", which $X declares" : " (mapped from $X's `$f`)"))
            continue
        end
        ST = fieldtype(T, g)
        FT = try
            _in_decision_world(field_type, X, Val(f), Kfull)
        catch e
            e isa MethodError || rethrow()
            # a parameter defined by matching a field's type, and the field's type does not match
            push!(ps, "field `$g` of $T has type `$ST`, which does not match the type $X declares for `$f`")
            continue
        end
        if w
            (ismutabletype(T) && !isconst(T, g)) ||
                push!(ps, "field `$f` is writable in $X, but $T's field `$g` cannot be written (an immutable type or a `const` field)")
            ST === FT || push!(ps, "field `$f` is writable in $X with type `$FT`, so $T's field `$g` must have exactly that type, not `$ST`")
        else
            ST <: FT || push!(ps, "field `$g` of $T has type `$ST`, but $X declares `$FT` for `$f`")
        end
        # a declared field's type is part of the key (decision 1)
        key_concrete(ST) || _concreteness_of(X) !== :concrete_only ||
            push!(ps, "field `$g` of $T has type `$ST`, which is not concrete, and $X asks for concrete keys (`@concrete_only`)")
    end
    return ps
end

"The representation a projection returns: declared, or inferred (must be concrete)."
function _rep_of(@nospecialize(f), @nospecialize(T), @nospecialize(Rdecl), Xs = ())
    Rinf = Base.infer_return_type(f, Tuple{T}; _check_kw()...)
    if Rdecl !== nothing
        Rinf <: Rdecl || throw(ImplementError("the projection of $T returns $Rinf, declared $Rdecl"))
        return Rdecl
    end
    # an abstract representation is an abstract key: allowed unless a trait asks for concrete keys
    abstract_ok = !isempty(Xs) && Rinf isa Type && Rinf !== Union{} && Rinf !== Any &&
                  all(X -> _concreteness_of(X) !== :concrete_only, Xs)
    isconcretetype(Rinf) || abstract_ok || throw(ImplementError(
        "cannot infer a concrete representation for the projection of $T (got $Rinf): declare it, as in `@implement Trait{R} $T …`"))
    return Rinf
end


# --- implementations as methods (keys-plan §6) -----------------------------------------

Base.Experimental.@max_methods 1 function _declared_defaults end
"""
`_declared_defaults(X, T)`: the operations a declared implementation of `X` for `T` serves by
defaults, as `(trait, receiver type, operations)` records, one method per implementation,
defined with it so that it is saved with the declaring package (note "Declaring a trait":
an override belongs to the implementation).
"""
_declared_defaults

"""
What an implementation's declaration fixes, after its checks: the builder of its views
(`nothing` when it must be built per session) and the operations its defaults serve,
without those the receiver type already had a method for.
"""
_declare_conformance(@nospecialize(X), @nospecialize(T)) = _latest(_declare_conformance_now, X, T)
@machinery function _declare_conformance_now(@nospecialize(X), @nospecialize(T))
    recs = Any[]
    (T isa DataType && isconcretetype(T)) || return (b = nothing, recs = ())
    p = proj_lookup(X, T)
    p === nothing && return (b = nothing, recs = ())
    for Y in trait_closure(X)
        w = Y === X ? proj_witness(X, T, p) : witness(Y, p.R)
        (w isa Impl && p.R !== Nothing) || continue
        D = Tuple(op for op in typeof(w).parameters[1] if !_has_op_method(Y, op, p.R))
        isempty(D) || push!(recs, (Y, p.R, D))
    end
    _refuse_overrides()
    return (b = _conformance_builder(X, T), recs = Tuple(recs))
end

"Whether `conformance(X, ::T)` has a method of its own (a declaration made it), not the fallback."
function _has_conformance_method(@nospecialize(X), @nospecialize(T))
    T isa Type || return false
    m = Base._which(Tuple{typeof(conformance),As{X},T}; raise = false)
    m === nothing && return false
    return Base.unwrap_unionall(m.method.sig).parameters[3] !== Any
end

"""
The statements that make an implementation a method: `conformance(X, u::T)` from a builder fixed now.
The method is part of the entry that calls it (a value crossing by its bound): a boundary, compiled
in its caller's mode and inlined there, so a typed call from plain code builds the trait object in
place.
"""
function _conformance_methods(Xex, Tex)
    TW = TraitWorld
    c = gensym(:conformance)
    return Any[:(const $c = $TW._declare_conformance($Xex, $Tex)),
               Expr(:macrocall, GlobalRef(Base, Symbol("@inline")), LineNumberNode(0, :none),
                    Expr(:function, :($TW.conformance(::$TW.As{$Xex}, u::$Tex)),
                         Expr(:block, Expr(:meta, :facts, 0), :($TW._conf_call($c.b, $Xex, u))))),
               :($TW._declared_defaults(::Type{$Xex}, ::Type{$Tex}) = $c.recs),
               :($TW._declared_builder(::$TW.As{$Xex}, ::Type{$Tex}) = $c.b),      # for the untyped calls' table (untyped.jl)
               :($TW._compile_ahead(@__MODULE__, $Xex, $Tex))]       # while its package is built: the code its calls need (ahead.jl)
end

"""
The statements that make a family's implementation a method: `conformance(X, u::T) where {…}` for
the whole family, with a registry of builders per member type in the declaring module. A member's
builder is found once on the slow path and kept there; builders found by the declaring package's
workload are saved with its image, so a session does not find them again (34 ms for the solver's
`FunctionModel` and integrator, session 27). A builder that holds a session's pointers is not kept.
A later declaration for one member is a more specific method. (A generator cannot fix the builder:
code reflection is not allowed in generated functions.)
"""
function _family_conformance_methods(@nospecialize(Xex), Tpat, wheres)
    TW = TraitWorld
    reg = gensym(:family_builders)
    return Any[
        :(const $reg = Ref($TW.IdDict{Any,Any}())),
        :($TW._family_registry(::Val{$(QuoteNode(reg))}) = $reg),      # found again after an image loads
        Expr(:(=), Expr(:where, :($TW.conformance(::$TW.As{$Xex}, u::$Tpat)), wheres...),
             :($TW._conf_family($reg, $Xex, u)))]
end
"`_family_registry(Val(name))`: a family implementation's builder registry, for the index of default-served operations."
function _family_registry end
"A family member's implementation: its kept builder, or the slow path, which keeps it."
@inline function _conf_family(reg::Base.RefValue{IdDict{Any,Any}}, ::Type{X}, u) where {X}
    b = get(reg[], typeof(u), nothing)
    b === nothing && return Base.inferencebarrier(_conf_family_slow)(reg, X, u)
    return (b::Builder)(u)
end
@machinery @noinline function _conf_family_slow(reg::Base.RefValue{IdDict{Any,Any}}, @nospecialize(X), @nospecialize(u))
    U = typeof(u)
    # a member at an abstract parameter (`S{Any}`) is refused at the entry where X asks for concrete keys
    _latest(_concreteness_of, X) === :concrete_only && !key_concrete(U) &&
        throw(TraitBoundError("a $U has an abstract type parameter, and $X asks for concrete keys (`@concrete_only`)"))
    r = _conformance_slow(X, u)                         # warns once for a member that does not conform
    b = r === NOTRAIT ? nothing : _latest(_family_builder, X, U)
    if b isa Builder
        @lock _LOCK begin
            d = copy(reg[])
            d[U] = b
            reg[] = d                                   # readers see the old table or the new one
        end
        # the member's implementation is now fixed: a later override of an operation its defaults
        # serve is refused, as for a single type's declaration (note "Declaring a trait")
        _OVR_BUILT[] && _index_builder!(X, U, b)
    end
    return r
end
"The builder of a family member's implementation, fixed when first compiled: `nothing` if it cannot be."
@machinery function _family_builder(@nospecialize(X), @nospecialize(U))
    (U isa DataType && isconcretetype(U)) || return nothing
    try
        # a member of a family declared by existing methods that does not conform (it breaks the
        # family's documented interface) keeps the slow path, which warns at its first use
        rec = _impl(X, U)
        if rec isa ImplRec && rec.kind === :family && !isempty(_ops(X))
            D = _existing_defaults(X, U)
            isempty(conformance_problems(X, U, Tuple(op for op in _ops(X) if !(op in D)))) || return nothing
        end
        b = _conformance_builder(X, U)
        return b isa Builder ? b : nothing
    catch
        return nothing
    end
end

"""
    check_overrides() -> Vector{String}

Methods of a trait's operation defined after an implementation whose default serves that
operation for the type (note "Declaring a trait": an override belongs to the implementation;
plain Julia would call the later method, so accepting it would break "identical or error").
Checked at every declaration, at the end of a trait module, after package loads and at a
worker signature's first call; refusing at the definition needs the runtime.
"""
function check_overrides()
    out = String[]
    for m in methods(_declared_defaults)
        sig = Base.unwrap_unionall(m.sig)
        ps = sig.parameters
        length(ps) == 3 || continue
        (ps[2] isa DataType && ps[3] isa DataType) || continue
        X, T = ps[2].parameters[1], ps[3].parameters[1]
        recs = _in_decision_world(_declared_defaults, X, T)
        for (Y, R, D) in recs
            for op in D
                _has_op_method(Y, op, R) || continue
                push!(out, "`$op` of $Y now has a method for $R, but the implementation of $X for $T serves it by the trait's default. " *
                           "An override belongs to the implementation, and a declared implementation cannot change (compiled code and kept values depend on it): " *
                   "define the method before `@implement`, or in its block, and restart the session")
            end
        end
    end
    for (Y, op, R, X, T) in _family_records()
        _has_op_method(Y, op, R) || continue
        push!(out, "`$op` of $Y now has a method for $R, but $R's implementation of $X, fixed at its first use, serves it by the trait's default. " *
                   "An override belongs to the implementation, and a fixed implementation cannot change: define the method before the type's first use, and restart the session")
    end
    return out
end
"Refuse overrides made after an implementation (see `check_overrides`)."
function _refuse_overrides()
    ps = check_overrides()
    isempty(ps) || throw(ImplementError(join(unique(ps), "\n  ")))
    return nothing
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
    # rule 3 before anything is defined: someone else's function (Base.size) may get a method
    # only for a representation the defining package owns
    if precheck && owner(parentmodule(f)) !== owner(mod)
        Rv = _tryeval(mod, Rex)
        if !(Rv isa Type && owner(mod) in sig_owners(Rv))
            throw(ImplementError(
                "$(mod) may not implement `$op` of $X for $(Rex): `$(nameof(f))` belongs to $(parentmodule(f)), and $(mod) does not own " *
                "$(Rex), so the method would change `$(nameof(f))` for everyone (rule 3). Declare the existing methods instead " *
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

"""
The implementation syntax of the design (note "How a type conforms to a trait"), lowered to the
forms below:
- `@implement X T begin ops end`: an implementation for `T` and its declaration, `X{P…, T}`;
- `@implement X A where {A <: …} [begin … end]`: a family or generic implementation;
- `@implement X T by f`: forwarding to the field `f`;
- `@implement X T dynamic by f begin ops on the field end`: the type's own operations on its field.
"""
function _keys_implement(mod::Module, args)
    length(args) >= 2 || return args
    head = args[1]
    X, pexs = (head isa Symbol || (head isa Expr && head.head === :.)) ? (head, Any[]) :
              head isa Expr && head.head === :curly ? (head.args[1], Any[head.args[2:end]...]) : (nothing, nothing)
    if X === nothing
        # several traits at once, `(ColTable, RowTable) T by f`: forwarding only
        head isa Expr && head.head === :tuple && length(args) == 4 && args[3] === :by && args[4] isa Symbol &&
            return (head, args[2], :(project(t) = getfield(t, $(QuoteNode(args[4])))))
        return args
    end
    Xv = try Core.eval(mod, X) catch; return args end
    Xv isa Type && Xv <: Trait || return args
    np = length(trait_params(Xv))
    # parameters left out are defined by the trait (an equation or a field)
    isempty(pexs) && np > 0 && (pexs = Any[:_ for _ in 1:np])
    length(pexs) == np || return args            # `X{P…, R}`: the earlier spelling
    T = args[2]
    rest = collect(args[3:end])
    # field mappings: `name => stored`, alone, in a tuple, or after `by f,`
    fmap = Any[]
    ispair(e) = e isa Expr && e.head === :call && e.args[1] === :(=>) && length(e.args) == 3
    if !isempty(rest) && rest[end] isa Expr && rest[end].head === :tuple && length(rest) >= 2 && rest[end-1] === :by
        tup = rest[end].args
        rest[end] = tup[1]
        append!(fmap, tup[2:end])
    end
    while !isempty(rest) && (ispair(rest[end]) || (rest[end] isa Expr && rest[end].head === :tuple && all(ispair, rest[end].args)))
        e = pop!(rest)
        ispair(e) ? pushfirst!(fmap, e) : prepend!(fmap, e.args)
    end
    if !isempty(fmap)
        all(ispair, fmap) && all(e -> e.args[2] isa Symbol && e.args[3] isa Symbol, fmap) ||
            error("@implement: a field mapping is `name => storedfield`")
        mapex = Expr(:fieldmap, [QuoteNode(e.args[2]) => QuoteNode(e.args[3]) for e in fmap]...)
        return (_keys_implement(mod, (args[1], T, rest...))..., mapex)
    end
    withR(R) = Expr(:curly, X, pexs..., R)
    # X A where {…}, with or without a block
    if T isa Expr && T.head === :where && T.args[1] isa Symbol
        return (Expr(:where, withR(T.args[1]), T.args[2:end]...), rest...)
    end
    # X T begin … end without `project`: an implementation for T
    if length(rest) == 1 && rest[1] isa Expr && rest[1].head === :block &&
       !any(d -> d isa Expr && d.args[1] isa Expr && d.args[1].args[1] in (:project, :unproject), _defs(rest[1]))
        return (withR(T), rest[1])
    end
    # forwarding: X T [dynamic] by f [block]
    flags = Any[]
    while !isempty(rest) && rest[1] isa Symbol && rest[1] !== :by
        push!(flags, popfirst!(rest))
    end
    if length(rest) >= 2 && rest[1] === :by && rest[2] isa Symbol
        f = rest[2]
        pdef = :(project(t) = getfield(t, $(QuoteNode(f))))
        if length(rest) == 3 && rest[3] isa Expr && rest[3].head === :block
            return (head, T, flags..., Expr(:block, pdef, rest[3].args...))
        end
        length(rest) == 2 || error("@implement: expected `@implement $X T by field`, optionally followed by a begin … end block")
        return isempty(flags) ? (head, T, pdef) : (head, T, flags..., Expr(:block, pdef))
    end
    return args
end

macro implement(args...)
    return _latest(_implement_expand, __module__, __source__.file, Any[args...])
end

# The expansion of `@implement`, and the checks its expansion runs, are compiled under the facts
# policy (`_latest`) and kept in TraitWorld's image: they reflect over expressions
# and types at abstract argument types, so their native code was invalidated by large loads and
# compiled again at the next `@implement` (0.6 s, 1.4-1.7 s after CSV, DataFrames and CairoMakie;
# session 26). Under the policy those calls dispatch at run time instead.
@machinery function _implement_expand(mod::Module, @nospecialize(file), argv::Vector{Any})
    _note_extension!(mod, file)
    TW = TraitWorld
    isempty(argv) && error("@implement: nothing to implement")
    args = _keys_implement(mod, (argv...,))
    fmap = nothing
    if !isempty(args) && args[end] isa Expr && args[end].head === :fieldmap
        fmap = Dict{Symbol,Symbol}(p.first.value => p.second.value for p in args[end].args)
        args = args[1:end-1]
    end
    head = args[1]
    rest = collect(args[2:end])
    # --- projections: @implement X T …, @implement (X, Y) T …, @implement X{R} T …
    if !isempty(rest) && !(rest[1] isa Expr && rest[1].head === :block)
        # an implementation declared again in the session, with a block of methods: refused with
        # the reason (design.md §4.4), not with what the block lacks
        if length(rest) >= 2 && rest[end] isa Expr && rest[end].head === :block
            X = try Core.eval(mod, head) catch; nothing end
            T = try Core.eval(mod, rest[1]) catch; nothing end
            if X isa Type && T isa Type && is_trait(X) && _has_conformance_method(X, T)
                throw(ImplementError("$T already conforms to $X: an implementation is not redeclared in a session. " *
                                     "An override of a default belongs to the implementation (the key and kept values depend on it); " *
                                     "to change it, change the declaration and restart Julia (redeclaration is not built yet)"))
            end
        end
        return _implement_projection(mod, head, rest; fmap)
    end
    fmap === nothing || error("@implement: a field mapping belongs to an implementation for a type, `@implement X T name => stored`")
    block = isempty(rest) ? nothing : rest[1]
    # --- generic and family implementations: X{R} where {...}
    if head isa Expr && head.head === :where
        return _implement_where(mod, head, block)
    end
    head isa Expr && head.head === :curly && length(head.args) >= 2 ||
        error("@implement: expected `Trait{R}`, `Trait{R} where {…}`, or `Trait T …`; got `$head`")
    X = Core.eval(mod, head.args[1])
    np = length(trait_params(X))
    length(head.args) == np + 2 ||
        error("@implement: $X takes $(np == 0 ? "the representation" : "$np parameter(s) and the representation, last"); got `$head`")
    Rex = head.args[end]
    if block !== nothing
        Rv = _tryeval(mod, Rex)
        Rv isa Type && _has_conformance_method(X, Rv) &&
            throw(ImplementError("$Rv already conforms to $X: an implementation is not redeclared in a session. " *
                                 "An override of a default belongs to the implementation (the key and kept values depend on it); " *
                                 "to change it, change the declaration and restart Julia (redeclaration is not built yet)"))
    end
    pdefs = _param_methods(X, head.args[2:end-1], Rex, Any[])
    if block === nothing
        # the representation's existing methods implement the trait (Base's, or its owner's)
        rec = gensym(:implementation)
        return esc(quote
            $(pdefs...)
            const $rec = $TW.ImplRec(:existing, ())
            $TW.implementation(::Type{$X}, ::Type{$Rex}) = $rec
            $TW._check_implementation(@__MODULE__, $X, $Rex,
                Tuple(op for op in $TW._ops($X) if !(op in $TW._existing_defaults($X, $Rex))))
            $(_has_conformance_method(X, _tryeval(mod, Rex)) ? nothing : Expr(:block, _conformance_methods(X, Rex)...))
            $TW._bump!()
            nothing
        end)
    end
    defs = _defs(block)
    given = Tuple(unique(_defname.(defs)))
    defaults = _missing_and_defaults(X, given)
    out = Any[pdefs...]
    append!(out, Any[_op_method(mod, X, d, Rex) for d in defs])
    rec = gensym(:implementation)
    push!(out, :(const $rec = $TW.ImplRec(:methods, $defaults)))
    push!(out, :($TW.implementation(::Type{$X}, ::Type{$Rex}) = $rec))
    push!(out, :($TW._check_implementation(@__MODULE__, $X, $Rex, $given)))
    _has_conformance_method(X, _tryeval(mod, Rex)) || append!(out, _conformance_methods(X, Rex))
    push!(out, :($TW._bump!()))
    push!(out, :nothing)
    return esc(Expr(:block, out...))
end

"The methods of `param` an implementation declares: parameter values at the representation `Rex`, under `wheres`."
function _param_methods(@nospecialize(X), pexs, Rex, wheres::Vector{Any})
    TW = TraitWorld
    ps = trait_params(X)
    length(pexs) == length(ps) || error("@implement: $X takes $(length(ps)) parameter(s), got $(length(pexs))")
    out = Any[]
    for (p, pex) in zip(ps, pexs)
        pex === :_ && continue              # defined by the trait's equation or field
        sig = :($TW.param(::Type{$X}, ::Val{$(QuoteNode(p))}, ::Type{$Rex}))
        push!(out, Expr(:(=), isempty(wheres) ? sig : Expr(:where, sig, wheres...), pex))
        # the same parameter at a key with declared fields, whose receiver type is Rex
        ksig = :($TW.param(::Type{$X}, ::Val{$(QuoteNode(p))}, ::Type{$TW.Key{$Rex,F__}}))
        push!(out, Expr(:(=), Expr(:where, ksig, wheres..., :F__), pex))
    end
    return out
end

"""
A family implementation: `@implement StateVector{T, Vector{T}} where {T <: Real} begin … end`
(the trait's parameters and the representation, a family of types), or without
a block the family's existing methods, as in the joint form
`@implement ArrayLike{T, 1} Series{T} where {T}`. Each member conforms at one
value of each parameter (associated types).
"""
function _implement_family(mod::Module, @nospecialize(X), tr, wheres::Vector{Any}, block)
    TW = TraitWorld
    np = length(trait_params(X))
    length(tr.args) == np + 2 || error("@implement: $X takes $np parameter(s) and the representation, last; got `$tr`")
    Rex = tr.args[end]
    out = _param_methods(X, tr.args[2:end-1], Rex, wheres)
    rec = gensym(:implementation)
    if block === nothing
        push!(out, :(const $rec = $TW.ImplRec(:family, ())))
    else
        defs = _defs(block)
        given = Tuple(unique(_defname.(defs)))
        defaults = _missing_and_defaults(X, given)
        for d in defs
            m = _op_method(mod, X, d, Rex)
            push!(out, Expr(m.head, Expr(:where, m.args[1], wheres...), m.args[2]))
        end
        push!(out, :(const $rec = $TW.ImplRec(:methods, $defaults)))
    end
    push!(out, Expr(:(=), Expr(:where, :($TW.implementation(::Type{$X}, ::Type{$Rex})), wheres...), rec))
    push!(out, :($TW._check_implementation(@__MODULE__, $X, $(Expr(:where, Rex, wheres...)), ())))
    append!(out, _family_conformance_methods(X, Rex, wheres))
    push!(out, :($TW._bump!()))
    push!(out, :nothing)
    return esc(Expr(:block, out...))
end

function _implement_where(mod::Module, head, block)
    TW = TraitWorld
    tr = head.args[1]
    if tr isa Expr && tr.head === :curly
        Xw = Core.eval(mod, tr.args[1])
        if !isempty(trait_params(Xw)) || !(length(tr.args) == 2 && tr.args[2] isa Symbol)
            return _implement_family(mod, Xw, tr, Any[head.args[2:end]...], block)
        end
    end
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
        isempty(family) || append!(out, _family_conformance_methods(X, Rsym, family))
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

"Whether `T` has methods for every operation of `X` that has no default."
_methods_cover(@nospecialize(X), @nospecialize(T)) =
    all(op -> _hasdefault(X, op) || _has_op_method(X, op, T), _ops(X))
_methods_some(@nospecialize(X), @nospecialize(T)) = any(op -> _has_op_method(X, op, T), _ops(X))

"""
The one-line form, `@implement Trait T`: methods of the trait's operations for
`T` make it its own representation, checked as an implementation; otherwise
the field named `data`, or the one field whose type conforms, is the
projection, composed with that type's own projection if it has one. Methods
win over a field; partial methods, several conforming fields without `data`,
or no conforming field are errors naming the operation or the fields.
"""
function _implement_oneline(mod::Module, traits::Vector{Any}, Tex, Rdecl; pexs = nothing, fmap = nothing)
    TW = TraitWorld
    Rdecl === nothing || error("@implement: the one-line form takes no representation; write `@implement $(traits[1]){$Rdecl} $Tex project(t) = …`")
    T = Core.eval(mod, Tex)
    T isa DataType && isconcretetype(T) ||
        error("@implement: the one-line form needs a concrete type, got `$Tex` (the prototype does not declare parametric families this way)")
    Xs = Any[Core.eval(mod, x) for x in traits]
    all(is_trait, Xs) || error("@implement: `$(traits[findfirst(!is_trait, Xs)])` is not a trait")
    # parameters the implementation states (`@implement ODEModel{Float64} Lorenz`): defined now, because
    # the checks below read the operations' declared types, which name them
    if pexs !== nothing
        for ex in _param_methods(Xs[1], pexs, Tex, Any[])
            Core.eval(mod, ex)
        end
        pexs = nothing
    end
    # a trait that declares its projection field (`data::R`) names the field
    pfs = unique(Symbol[f for X in Xs for (f, _) in trait_fields(X) if field_isrep(X, Val(f))])
    if !isempty(pfs)
        length(pfs) == 1 || throw(ImplementError("$(join(string.(Xs), ", ")) declare different projection fields: $(join(string.(pfs), ", "))"))
        f = pfs[1]
        hasfield(T, f) || throw(ImplementError("$Tex has no field `$f`, which $(join(string.(Xs), ", ")) declares as its projection"))
        headex = length(traits) == 1 ? traits[1] : Expr(:tuple, traits...)
        return _implement_projection(mod, headex, Any[Tex, :(project(t) = getfield(t, $(QuoteNode(f))))]; field = Base.fieldindex(T, f), fmap)
    end
    if all(X -> _methods_cover(X, T), Xs)
        # the type implements the operations itself: its existing methods, checked as an implementation
        out = Any[]
        if fmap !== nothing || any(X -> isempty(_ops(X)) && !isempty(trait_fields(X)), Xs)
            # a declared implementation with its field mapping (a trait with fields only conforms this way too)
            for (xex, X) in zip(traits, Xs)
                prec = gensym(:conformance)
                Iex = isempty(_ops(X)) ? :Nothing : Tex
                push!(out, :(const $prec = $TW.ProjRec(identity, $Iex, false, nothing, 0, nothing, $(fmap === nothing ? :nothing : QuoteNode(fmap)))))
                push!(out, :($TW.projection(::Type{$xex}, ::Type{$Tex}) = $prec))
                push!(out, :($TW._check_projection(@__MODULE__, $xex, $Tex)))
            end
        end
        pexs === nothing || append!(out, _param_methods(Xs[1], pexs, Tex, Any[]))
        for (xex, X) in zip(traits, Xs)
            rec = gensym(:implementation)
            push!(out, :(const $rec = $TW.ImplRec(:existing, ())))
            push!(out, :($TW.implementation(::Type{$xex}, ::Type{$Tex}) = $rec))
            push!(out, :($TW._check_implementation(@__MODULE__, $xex, $Tex,
                           Tuple(op for op in $TW._ops($xex) if !(op in $TW._existing_defaults($xex, $Tex))))))
            # the one-line form declares that the type conforms: it must have the declared fields
            fmap === nothing && push!(out, :($TW._check_own_fields($xex, $Tex)))
            _has_conformance_method(X, T) || append!(out, _conformance_methods(xex, Tex))
        end
        push!(out, :($TW._bump!()))
        push!(out, :nothing)
        return esc(Expr(:block, out...))
    end
    for X in Xs
        if _methods_some(X, T)
            missing_ops = [op for op in _ops(X) if !_hasdefault(X, op) && !_has_op_method(X, op, T)]
            throw(ImplementError("$Tex has methods for some operations of $X but not for $(join(string.(missing_ops), ", ")): " *
                                 "define them, so that $Tex is its own representation, or remove them and conform through a field"))
        end
    end
    fns = fieldnames(T)
    conforming = Int[]
    abstract_conforming = Int[]
    for i in 1:fieldcount(T)
        FT = fieldtype(T, i)
        FT isa Type || continue
        all(X -> witness(X, FT) !== nothing, Xs) || continue
        # a concrete field first; an abstract one where the traits allow abstract keys
        key_concrete(FT) ? push!(conforming, i) : push!(abstract_conforming, i)
    end
    idata = findfirst(==(:data), fns)
    fld = if idata !== nothing && idata in conforming
        idata
    elseif length(conforming) == 1
        conforming[1]
    elseif isempty(conforming)
        if !isempty(abstract_conforming)
            i = abstract_conforming[1]
            if length(abstract_conforming) == 1 && all(X -> _concreteness_of(X) !== :concrete_only, Xs)
                i
            else
                throw(ImplementError("field `$(fns[i])` of $Tex is declared `$(fieldtype(T, i))`, which is not concrete, and " *
                                     "$(join(string.(Xs), ", ")) asks for concrete keys (`@concrete_only`): declare a concrete field type, " *
                                     "or write a projection that materializes it"))
            end
        else
        throw(ImplementError("$Tex does not conform to $(join(string.(Xs), ", ")): it does not implement " *
                             "the operations, and no field of it conforms " *
                             "(fields: $(join(("$n::$(fieldtype(T, i))" for (i, n) in enumerate(fns)), ", "))). Required:\n  " *
                             join((_required_ops_text(X, T) for X in Xs), "\n  ") *
                             "\nImplement these for $Tex, or forward to a field whose type conforms (`@implement $(traits[1]) $Tex by field`)"))
        end
    else
        throw(ImplementError("several fields of $Tex conform to $(join(string.(Xs), ", ")): $(join(string.(fns[conforming]), ", ")). " *
                             "Name one `data`, or choose one: `@implement $(traits[1]) $Tex by field`"))
    end
    FT = fieldtype(T, fld)
    fsym = QuoteNode(fns[fld])
    # the field's type must implement the trait itself: forwarding does not chain
    any(X -> _proj(X, FT) !== nothing, Xs) && throw(ImplementError(
        "field `$(fns[fld])` of $Tex forwards $(join(string.(Xs), ", ")) to a field of its own; forward to a field whose type implements the operations"))
    headex = length(traits) == 1 ? traits[1] : Expr(:tuple, traits...)
    return _implement_projection(mod, headex, Any[Tex, :(project(t) = getfield(t, $fsym))]; field = fld, fmap)
end

"The field a projection body reads from its argument as is (`t.cols`, `getfield(t, :cols)`), or nothing."
function _field_read(body, tname)
    while body isa Expr && body.head === :block
        stmts = filter(x -> !(x isa LineNumberNode), body.args)
        length(stmts) == 1 || return nothing
        body = stmts[1]
    end
    body isa Expr || return nothing
    body.head === :. && body.args[1] === tname && body.args[2] isa QuoteNode && return body.args[2].value
    body.head === :call && body.args[1] === :getfield && length(body.args) == 3 && body.args[2] === tname &&
        body.args[3] isa QuoteNode && return body.args[3].value
    return nothing
end

function _implement_projection(mod::Module, head, rest; field::Int = 0, fmap = nothing)
    TW = TraitWorld
    traits = Any[]
    Rdecl = nothing
    pexs = nothing
    if head isa Expr && head.head === :tuple
        append!(traits, head.args)
    elseif head isa Expr && head.head === :curly
        push!(traits, head.args[1])
        np = length(trait_params(Core.eval(mod, head.args[1])))
        a = head.args[2:end]
        if np > 0 && length(a) == np
            pexs = a                              # the trait's parameters: `@implement ArrayLike{Float64, 1} MyVector`
        elseif length(a) == np + 1
            np > 0 && (pexs = a[1:np])
            Rdecl = a[end]
        else
            error("@implement: $(head.args[1]) takes $np parameter(s)" * (np > 0 ? ", then optionally the representation" : " and the representation"))
        end
    else
        push!(traits, head)
    end
    Tex = popfirst!(rest)
    if Tex isa Expr && Tex.head === :where && isempty(rest)
        # the joint family form: `@implement ArrayLike{T, 1} Series{T} where {T}`, the type its own representation
        X = Core.eval(mod, traits[1])
        if pexs === nothing
            # a family conforming by its fields: the trait's parameters are defined by the fields' types
            all(q -> q in _in_decision_world(trait_field_params, X), trait_params(X)) ||
                error("@implement: a family `$Tex` needs the trait's parameters")
            Tb, wh = Tex.args[1], Tex.args[2:end]
            Iex = isempty(_ops(X)) ? :Nothing : Tb
            fex = fmap === nothing ? :nothing : QuoteNode(fmap)
            return esc(Expr(:block,
                Expr(:(=), Expr(:where, :($TW.implementation(::Type{$(traits[1])}, ::Type{$Tb})), wh...), :($TW.ImplRec(:family, ()))),
                Expr(:(=), Expr(:where, :($TW.projection(::Type{$(traits[1])}, ::Type{$Tb})), wh...),
                     :($TW.ProjRec(identity, $Iex, false, nothing, 0, nothing, $fex))),
                _family_conformance_methods(X, Tb, wh)...,
                :($TW._bump!()), :nothing))
        end
        return _implement_family(mod, X, Expr(:curly, traits[1], pexs..., Tex.args[1]), Any[Tex.args[2:end]...], nothing)
    end
    flags = Symbol[]
    while !isempty(rest) && _flag(rest[1])
        push!(flags, popfirst!(rest))
    end
    isempty(rest) && isempty(flags) && return _implement_oneline(mod, traits, Tex, Rdecl; pexs, fmap)
    length(rest) == 1 || error("@implement: expected `project(t) = …` or a begin … end block after the type")
    body = rest[1]
    dynamic = :dynamic in flags
    copies = :copies in flags
    defs = body isa Expr && body.head === :block ? _defs(body) : Any[body]
    pdefs = filter(d -> d isa Expr && d.args[1] isa Expr && d.args[1].args[1] === :project, defs)
    length(pdefs) == 1 || error("@implement: a projection needs exactly one `project(t) = …`")
    pdef = pdefs[1]
    udefs = filter(d -> d isa Expr && d.args[1] isa Expr && d.args[1].args[1] === :unproject, defs)
    length(udefs) <= 1 || error("@implement: at most one `unproject(t, r) = …`")
    ops = filter(d -> d !== pdef && !(d in udefs), defs)
    pcall = pdef.args[1]
    length(pcall.args) == 2 || error("@implement: `project` takes the value only")
    targ = pcall.args[2]
    tname = targ isa Expr ? targ.args[1] : targ
    copies && throw(ImplementError("copying projections are not part of the design; a library converts explicitly (note \"Types that only convert\")"))
    isempty(udefs) || throw(ImplementError("`unproject` is gone with computed projections; a result like the input replaces fields"))
    if field == 0
        # forwarding: the projection reads a field as is (`by data`, or `project(t) = t.data`)
        f = _field_read(pdef.args[2], tname)
        T = f === nothing ? nothing : Core.eval(mod, Tex)
        T isa Type && f in fieldnames(T) && (field = Base.fieldindex(T, f))
    end
    field == 0 && throw(ImplementError("`$(pdef.args[1]) = …` computes a value: a type conforms by implementing the operations or by " *
                        "forwarding them to a field (`@implement X T by field`); a library that needs another layout converts explicitly " *
                        "(note \"Types that only convert\")"))
    pfn = gensym(:project)
    rec = gensym(:projection)
    Rconst = gensym(:R)
    out = Any[]
    push!(out, Expr(:function, Expr(:call, pfn, :($tname::$Tex)), pdef.args[2]))
    invex = :nothing
    if !isempty(udefs)
        # the inverse of the projection: a value of the user's type from a representation
        ucall = udefs[1].args[1]
        length(ucall.args) == 3 || error("@implement: `unproject` takes the value and a representation, `unproject(t, r)`")
        ufn = gensym(:unproject)
        push!(out, Expr(:function, Expr(:call, ufn, ucall.args[2:end]...), udefs[1].args[2]))
        invex = ufn
    end
    push!(out, :(const $Rconst = $TW._rep_of($pfn, $Tex, $(Rdecl === nothing ? nothing : Rdecl), ($(traits...),))))
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
    push!(out, :(const $rec = $TW.ProjRec($pfn, $Rconst, $copies, $dynex, $field, $invex, $(fmap === nothing ? :nothing : QuoteNode(fmap)))))
    for X in traits
        push!(out, :($TW.projection(::Type{$X}, ::Type{$Tex}) = $rec))
    end
    for X in traits
        push!(out, :($TW._check_projection(@__MODULE__, $X, $Tex)))
    end
    for X in traits
        _has_conformance_method(_tryeval(mod, X), _tryeval(mod, Tex)) || append!(out, _conformance_methods(X, Tex))
    end
    push!(out, :($TW._bump!()))
    push!(out, :nothing)
    return esc(Expr(:block, out...))
end

@specialize
