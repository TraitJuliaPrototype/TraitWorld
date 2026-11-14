# like and withfields (traits §6.5; lowering §8).

"""
    like(t, x)

A value like `t`, built from `x`: where `t`'s type serves its trait by its own methods, `x`
itself (of `t`'s type family); where it forwards by a field, `t`'s type rebuilt by its
positional constructor with the forwarding field replaced by `x`; on a `Dynamic{X}`, a
`Dynamic{X}` of `x`.
"""
function like(t, x)
    t isa Dynamic && return typeof(t)(x)
    S = typeof(t)
    f = get(_FORWARD_FIELD, S.name, nothing)
    if f === nothing
        typeof(x).name === S.name ||
            throw(ArgumentError("like(t, x): t's type $S serves its trait by its own methods, so x must be of its family, $(S.name.wrapper); got $(typeof(x))"))
        return x
    end
    vals = Any[getfield(t, i) for i in 1:fieldcount(S)]
    vals[Base.fieldindex(S, f)] = x
    return _rebuild(S, vals)
end

"""
    withfields(t; name = v, …)

`t` rebuilt by its type's positional constructor, with the named fields replaced.
"""
function withfields(t; kw...)
    S = typeof(t)
    for k in keys(kw)
        hasfield(S, k) || throw(ArgumentError("withfields: $S has no field $k"))
    end
    vals = Any[haskey(kw, n) ? kw[n] : getfield(t, n) for n in fieldnames(S)]
    return _rebuild(S, vals)
end

function _rebuild(S::DataType, vals::Vector{Any})
    C = S.name.wrapper
    if !hasmethod(C, Tuple{map(typeof, vals)...})
        want = string(nameof(C), "(", join(("::" * _tstr(typeof(v)) for v in vals), ", "), ")")
        throw(ArgumentError("`like` and `withfields` rebuild a $(nameof(C)) by its positional constructor, with every field in order; " *
                            "$(nameof(C)) has no method `$want`. Define one (an inner constructor has replaced the default)"))
    end
    return C(vals...)
end
