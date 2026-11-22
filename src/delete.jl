# Taking a membership back (traits §5.13; facts §10; compiler §4.3, §5.5; lowering §3): as a method's
# deletion. The membership of `S` in `X` that an `@implement` declared ends from the next world on; the
# code that relied on it is compiled again, and no other code is.

"""
    delete_membership(X, S; by = <the declaring module>)

Take back the membership of `S` in the trait `X` that an `@implement` declared, as `Base.delete_method(m)`
deletes a method (traits §5.13). From the next world on `S` is no member: the code that relied on the
membership is compiled again, a call that dispatched to `S`'s own method keeps its code, and a task in an
older world keeps the membership. `S` is the member as declared (a type, a family `S{T} where T`, an
abstract type or a trait); `X` names the trait, at the input values that select the membership where the
trait has inputs.

Whoever may declare it may take it back (traits §12.1): `by` is the module that takes it back, by default
the one that declared it. One by neither the trait's owner nor the type's is a pirate's: refused in a
scope that declares `no_pirates`, refused in strict mode where code compiled by facts relies on it.
Not taken back alone: a member by its definition (`struct S <: X`), a trait's membership in its
supertraits, and `Dynamic{X}`'s and `Compiled`'s.
"""
function delete_membership(@nospecialize(X), @nospecialize(S); by::Union{Module,Nothing} = nothing)
    istrait(X) || throw(ArgumentError("delete_membership: $X is not a trait"))
    Xname = (Base.unwrap_unionall(bare(X))::DataType).name
    core = Base.unwrap_unionall(S)
    core isa DataType || throw(ArgumentError("delete_membership: the member is a type or a family of types; got $S"))
    # the membership's own forms: the box's, the wrapper's, a supertrait's (traits §5.13)
    (core.name === Base.unwrap_unionall(Dynamic).name || core.name === Base.unwrap_unionall(Compiled).name) &&
        throw(ImplementError(X, S, "$(core.name.name)'s membership is the trait's declaration and is not taken back alone"))
    if istrait(core)
        c = contract(core)
        if c !== nothing
            for s in c.supers
                s isa Type && bare(s) === bare(X) &&
                    throw(ImplementError(X, S, "a trait's membership in its supertrait is its declaration and is not taken back alone"))
            end
        end
    end
    # a member by its definition (traits §5.2)
    d = core.super
    while d isa DataType && d !== Any
        d.name === Xname && throw(ImplementError(X, S,
            "$(core.name.name) is a member of $(Xname.name) by its definition: only a new definition of $(core.name.name) changes its supertype"))
        d = d.super
    end
    en = _entry_in_force(core, Xname, S, X)
    en === nothing && throw(ImplementError(X, S, "no membership of $S in $(bare(X)) is in force to take back"))
    inst = getfield(en, :instance)
    declarer = getfield(en, :declarer)::Module
    mod = by === nothing ? declarer : by
    # who may: whoever may declare it (traits §12.1, §12.2)
    definer = owner(mod)
    pirate = !(owns(definer, _type_owner(bare(X))) || owns(definer, _type_owner(S)))
    if pirate
        what = "delete_membership($(bare(X)), $S) by $mod: $(_owner_name(definer)) owns neither the trait nor the type"
        _no_pirates(mod) && throw(OwnershipError(what * ": a pirate's, and the scope declares `no_pirates`"))
        STRICT[] && _strict_take_back!(en, S, inst, mod, definer)
        _runtime_site(() -> @warn what * ": a pirate's. It is followed; the code that relied on the membership is compiled again.")
    end
    ccall(:jl_delete_membership, Cvoid, (Any, Any, Any), getfield(en, :member), inst, mod)
    _forget_membership!(X, getfield(en, :member), inst)
    _report_now!()                       # a pirate's take-back that ended deep code (traits §12.2)
    return nothing
end

# the entry in force of `S` (as declared) in `X`, on its TypeName's list; of several (a trait with inputs),
# the one at the instance `X` names
function _entry_in_force(core::DataType, Xname::Core.TypeName, @nospecialize(S), @nospecialize(X))
    home = core.name === Type.body.name && length(core.parameters) == 1 ?
           (Base.unwrap_unionall(core.parameters[1])::DataType).name : core.name
    cands = Any[]
    for en in getfield(home, :memberships, :acquire)
        getfield(en, :set) === Xname || continue
        getfield(en, :max_world, :acquire) == typemax(UInt64) || continue
        getfield(en, :member) == S || continue
        push!(cands, en)
    end
    length(cands) <= 1 && return isempty(cands) ? nothing : cands[1]
    for en in cands
        inst = getfield(en, :instance)
        (inst <: X || X <: inst) && return en
    end
    return cands[1]
end

# The library's records of the membership (traits §5.10, §5.11; lowering §3, step 7) and its kept check
# answers (compiler §10.4, `_CHECKED`), for each member a pattern made; its pattern for first uses.
function _forget_membership!(@nospecialize(X), @nospecialize(member), @nospecialize(inst))
    Xb = bare(X)
    for key in _runtime_site(collect, keys(_CHECKED))      # Base's walk of an `IdDict{Any}` (W-167)
        T, Y = key
        Y === Xb && T isa Type && T <: member && delete!(_CHECKED, key)
    end
    for recs in _FIXED_LISTS
        _forget_under!(recs, member, Xb)
    end
    for recs in _CHECKED_LISTS
        _forget_under!(recs, member, Xb)
    end
    j = 0
    for i in eachindex(_PATTERNS)
        p = _PATTERNS[i]
        (p[1] == member && bare(p[2]) === Xb) && continue
        j += 1
        _PATTERNS[j] = p
    end
    resize!(_PATTERNS, j)
    delete!(_IMPLEMENTED, (Base.unwrap_unionall(member).name, Base.unwrap_unionall(Xb).name))
    return nothing
end

function _forget_under!(recs::Vector{Any}, @nospecialize(member), @nospecialize(Xb))
    j = 0
    for i in eachindex(recs)
        r = recs[i]
        m = getfield(r, :member)
        (getfield(r, :trait) === Xb && m isa Type && m <: member) && continue
        j += 1
        recs[j] = r
    end
    resize!(recs, j)
    return nothing
end

# Strict mode (traits §12.3, facts §11.3): a pirate's take-back is refused, as a method's deletion is,
# where code compiled by facts in the deep class relies on it: code that folded the positive (an edge to
# the membership's method), or a call at the member that selected a method at the trait.
function _strict_take_back!(en, @nospecialize(S), @nospecialize(inst), mod::Module, @nospecialize(definer))
    pm = PirateMembership(bare(getfield(en, :instance)), S, mod)
    m = getfield(en, :method)
    seen = Set{Core.CodeInstance}()
    if m isa Method
        for mi in Base.specializations(m)
            mi isa Core.MethodInstance && isdefined(mi, :backedges) || continue
            for x in mi.backedges
                x isa Core.CodeInstance || continue
                c = _facts_dependent(x, seen)
                c === nothing || throw(PirateError(pm, definer, m.sig, c, false))
            end
        end
    end
    rs = ccall(:jl_membership_replay_sigs, Any, (Any, Any), getfield(en, :member), inst)::Vector{Any}
    for i in 1:2:length(rs)-1
        tm, sig = rs[i]::Method, rs[i+1]
        for mi in Base.specializations(tm)
            mi isa Core.MethodInstance && isdefined(mi, :backedges) || continue
            sig isa Type && !(mi.specTypes <: sig) && typeintersect(mi.specTypes, sig) === Union{} && continue
            for x in mi.backedges
                x isa Core.CodeInstance || continue
                c = _facts_dependent(x, seen)
                c === nothing || throw(PirateError(pm, definer, mi.specTypes, c, false))
            end
        end
    end
    return nothing
end
