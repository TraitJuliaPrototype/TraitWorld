# Compiling ahead (traits §16; lowering §12). While a package that declares `@implement X S` is
# precompiled, the code `S` needs is compiled into that package's image: every method at `X` or a
# supertrait with one trait argument, fully bounded there, at `S`, where the other arguments are
# concrete (a `Dynamic` argument's instance is the one at the set); and the operations' methods at `S`,
# the targets of a call through the trait. Compiling ahead adds no method, so it invalidates nothing.
# `JULIA_TW_AHEAD=0` turns it off.

_ahead_on() = ccall(:jl_generating_output, Cint, ()) == 1 && get(ENV, "JULIA_TW_AHEAD", "1") != "0"

"The methods whose signatures name the set `X` (the runtime's set-to-methods index, compiler §5.1)."
function set_methods(@nospecialize(X))
    tn = (Base.unwrap_unionall(bare(X))::DataType).name
    ms = ccall(:jl_open_set_methods_of, Any, (Any,), tn)
    return ms isa Vector ? ms : Any[]
end

"""
The compile requests for `S` as a member of the trait instance `inst` (traits §16): each a signature,
with the trait argument's bit where the request is for a method at the set (`0` for an operation's
method at `S`). `ahead_requests(inst, S)` lists them; while a package is precompiled `@implement`
compiles them.
"""
function ahead_requests(@nospecialize(inst), @nospecialize(S))
    out = Pair{Any,UInt32}[]
    (S isa DataType && isconcretetype(S)) || return out
    for (c, env) in _contracts_of(inst)
        Xs = bare(c.trait)
        for m in set_methods(Xs)
            m isa Method || continue
            r = _ahead_sig(m, Xs, S)
            r === nothing || any(p -> p.first == r.first, out) || push!(out, r)
        end
        # the targets of a call through the trait: the operations' methods at S (compiler §7.3)
        for op in c.operations
            tt = _call_types(c, op, env, S)
            tt === nothing && continue
            T = Tuple{Core.Typeof(op.f), (tt::Type{<:Tuple}).parameters...}
            Base.isdispatchtuple(T) && !any(p -> p.first == T, out) && push!(out, T => UInt32(0))
        end
    end
    return out
end

# a method at the set Xs with one trait argument, fully bounded there, and concrete other arguments:
# its signature at S, or `nothing`
function _ahead_sig(m::Method, @nospecialize(Xs), @nospecialize(S))
    _is_trait_method(m) && return nothing                    # the contract's own method
    sig = Base.unwrap_unionall(m.sig)
    sig isa DataType || return nothing
    ps = sig.parameters
    tpos = Int[]
    for i in 2:length(ps)
        p = ps[i]
        Base.isvarargtype(p) && return nothing
        _trait_of(p isa TypeVar ? p.ub : p) === nothing || push!(tpos, i)
    end
    length(tpos) == 1 || return nothing                     # several trait arguments: at the first call
    k = tpos[1]
    d = ps[k] isa TypeVar ? ps[k].ub : ps[k]
    bare(d) === Xs || return nothing
    S <: (Base.has_free_typevars(d) ? bare(d) : d) || return nothing
    for i in 1:length(ps)
        i == k && continue
        (ps[i] isa Type && isconcretetype(ps[i])) || return nothing
    end
    isempty(classify(m)) || return nothing                   # open: compiled at its first call
    return Tuple{ps[1:k-1]..., S, ps[k+1:end]...} => UInt32(1) << (k - 2)
end

"""
Compile ahead for a membership, while a package image is written (lowering §12): at a method at the
set, the instance a static call at `S` runs (compiler §6.3): compiled for `S`, or once at the set where
the method's own attribute is `Dynamic`.
"""
function _compile_ahead!(@nospecialize(inst), @nospecialize(S))
    _ahead_on() || return 0
    n = 0
    world = Base.get_world_counter()
    for (T, bit) in ahead_requests(inst, S)
        ok = if bit == 0
            precompile(T)
        else
            m = Base._which(T; world).method
            dyn = ccall(:jl_attribute_dynamic_bits, UInt32, (Any, Any, UInt32, UInt32), T, m, 0, 0) & bit
            mi = ccall(:jl_attributed_mi, Any, (Any, UInt32, UInt32, UInt), T, bit, dyn, world)
            mi isa Core.MethodInstance && precompile(mi)
        end
        n += ok ? 1 : 0
    end
    return n
end
