# ---------------------------------------------------------------------------
# What library code may do with a trait object (rule 2 and the "may do"
# table), checked on the worker's typed code at a concrete representation:
# a `TObj` may reach only methods declared for trait objects, which are the
# trait's operations and workers whose bounds it carries. Anything else, a
# builtin (`t.field`, `typeof(t)`, storing it in a tuple), an ordinary
# function (`sum(t)`) or the entry of a function bounded by another trait, is
# reported with its line. Workers called from workers are checked too.
# ---------------------------------------------------------------------------

const _CC = Core.Compiler

struct TraitUseError <: Exception
    problems::Vector{String}
end
function Base.showerror(io::IO, e::TraitUseError)
    print(io, "TraitUseError: library code breaks a rule of the trait world:")
    for p in e.problems
        print(io, "\n  ", p)
    end
end

_istobj(@nospecialize(T)) = T isa DataType && T.name === Base.typename(TObj)
_hastobj(@nospecialize(T)) = _istobj(T) || (T isa Union && any(_istobj, Base.uniontypes(T)))

function _line_of(src, mi, i)
    try
        lin = Base.IRShow.buildLineInfoNode(src.debuginfo, mi, i)
        if !isempty(lin)
            n = lin[end]
            return string(basename(string(n.file)), ":", n.line)
        end
    catch
    end
    m = mi isa Core.MethodInstance ? mi.def : nothing
    return m isa Method ? string(basename(string(m.file)), ":", m.line) : "?"
end

"Whether method `m` is code of a trait module (defined in one, or in a module inside one)."
function _is_trait_module_code(m::Method)
    x = m.module
    while true
        isdefined(x, :__trait_module__) && return true
        p = parentmodule(x)
        p === x && return false
        x = p
    end
end

"Whether `f` is an operation function of one of the traits in `lb` (its methods on trait objects forward)."
function _is_op(@nospecialize(f), @nospecialize(lb))
    for X in Base.uniontypes(lb)
        X = _family(X)
        is_trait(X) || continue
        for op in _ops(X)
            _opfn(X, op) === f && return true
        end
    end
    return false
end

"`Type{<:TObj}` or `Type{<:CObj}`: a declaration of the machinery's own types, not a look at the user's."
_handle_type(@nospecialize(T)) = T isa DataType && T <: Type && (T.parameters[1] <: TObj || T.parameters[1] <: CObj)

_traitnames(@nospecialize(T)) = _istobj(T) ? join(unique(string.(_family.(Base.uniontypes(_decode_traits(T.parameters[1]))))), ", ") : string(T)

"""
    worker_problems(sig) -> Vector{String}

Problems in the worker selected by the concrete call signature `sig`, and in
the workers it calls.
"""
_escapes(@nospecialize(T)) = T isa Union ? any(_escapes, Base.uniontypes(T)) :
    (T isa DataType && (T <: TObj || T <: AbstractView || T <: CObj || T <: CMulti || T <: LikeResult ||
                        (T <: Tuple && any(_escapes, T.parameters))))

@machinery function worker_problems(@nospecialize(sig), seen = Base.IdSet{Any}(), out = String[]; root::Bool = true)
    sig in seen && return out
    push!(seen, sig)
    return _worker_problems(sig, seen, out, root)
end

function _worker_problems(@nospecialize(sig), seen, out, root::Bool)
    world = Base.get_world_counter()
    # the default interpreter: a worker (a facts method) is reflected by facts inference, the code
    # that runs, typed at facts only and cached where the worker's own compilation finds it (and its
    # package image keeps it). The checks' interpreter inferred the whole call graph again under
    # plain rules (3,100 CodeInstances for the forks' first `stringtype = String15` read: 1.6 s).
    for (src, rt) in Base.code_typed_by_type(sig; optimize = false, world)
        mi = src.parent
        if root && _escapes(rt) && !(mi isa Core.MethodInstance && mi.def isa Method &&
                                     Base.unwrap_unionall(mi.def.sig).parameters[1] in _LIKE_FUNCS)
            m = mi isa Core.MethodInstance ? mi.def : nothing
            push!(out, "$(m isa Method ? string(basename(string(m.file)), ":", m.line) : "?"): returns a trait object " *
                       "to ordinary code: a trait object is a handle, not a value")
        end
        sptypes = mi isa Core.MethodInstance ? _CC.sptypes_from_meth_instance(mi) : _CC.EMPTY_SPTYPES
        for (i, st) in enumerate(src.code)
            ex = st isa Expr && st.head === :(=) ? st.args[2] : st
            if ex isa Expr && ex.head === :new
                # a closure capturing a trait object: its body runs wherever it is called
                # (inside Base's `sum`, say), so check it here, for any arguments
                CT = _CC.argextype(ex.args[1], src, sptypes)
                CT = CT isa _CC.Const ? CT.val : _CC.widenconst(CT)
                CT isa Type && CT <: Type && (CT = CT.parameters[1])
                if CT isa DataType && CT <: Function && any(k -> _hastobj(fieldtype(CT, k)), 1:fieldcount(CT))
                    for mm in Base._methods_by_ftype(Tuple{CT,Vararg{Any}}, -1, world)
                        n = mm.method.nargs - 1
                        worker_problems(Tuple{CT,ntuple(_ -> Any, n)...}, seen, out)
                    end
                end
                continue
            end
            ex isa Expr && ex.head === :call || continue
            ats = Any[_CC.widenconst(_CC.argextype(a, src, sptypes)) for a in ex.args]
            fT = _CC.argextype(ex.args[1], src, sptypes)
            f = fT isa _CC.Const ? fT.val : (Base.issingletontype(_CC.widenconst(fT)) ? _CC.widenconst(fT).instance : nothing)
            # a call without trait objects: any Julia code (wrapping by facts)
            any(k -> _hastobj(ats[k]), 2:length(ats)) || continue
            line = _line_of(src, mi, i)
            # a field its traits declare: `t.f`, and `t.f = x` unless the field is `const`
            if (f === Base.getproperty || f === Base.setproperty!) && length(ats) >= 3 && _istobj(ats[2])
                nm = _CC.argextype(ex.args[3], src, sptypes)
                fname = nm isa _CC.Const ? nm.val : nothing
                fname isa Symbol && _declares_field(ats[2], fname, f === Base.setproperty!) && continue
                push!(out, "$line: `t.$(something(fname, "field"))`" * (f === Base.setproperty! ? " = …" : "") *
                           ": the user's data is reached only through the operations and the writable fields its traits declare (" *
                           _declared_text(ats[2]) * ")")
                continue
            end
            # keeping a trait object where a Dynamic is declared (note "Dynamic values")
            _keeps_dynamic(f, ats, ex, src, sptypes) && continue
            # the conversions (traits reference §6.6), and the test of a trait object's attribute
            (f === compiled_for || f === with_dynamic || f === is_dynamic) && continue
            # a struct parameter bounded by a trait keeps the value in its stored form (traits reference §10.4)
            (f === _kept_at || f === _known_type) && continue
            f isa Type && bounded_constructor(f) && continue        # its constructor is the bound
            # a result like the input, which only the entry inverts
            (f === like || f === withfields || (f isa Type && f <: LikeResult) ||
             (f === Core.kwcall && length(ats) >= 3 && _CC.widenconst(ats[3]) === typeof(withfields))) && continue
            if f === nothing
                push!(out, "$line: a trait object is passed to a function not known at compile time")
                continue
            end
            fname = f isa Function ? nameof(f) : f
            f === Core._typeof_captured_variable && continue      # closure lowering: the closure body is checked at its `new`
            if (f === Core.isa || f === Core.typeassert) && length(ats) == 3 && _handle_type(ats[3])
                continue                                           # a keyword sorter's own check of a bounded keyword
            end
            if f isa Core.Builtin || f isa Core.IntrinsicFunction
                what = f === Core.getfield ? "`t.field`: the user's data is reached only through the trait's operations" :
                       f === Core.typeof ? "`typeof(t)`: code must not depend on the user's type" :
                       f === Core.tuple ? "stored in a tuple: a trait object is a handle, not a value" :
                       f === Core._apply_iterate ? "splatted into a call" :
                       "passed to the builtin `$fname`"
                push!(out, "$line: $what")
                continue
            end
            # an operation called on a trait object: its other arguments are checked against the declaration
            # at the call, where a trait object is accepted only for an argument declared `Dynamic{Y}`,
            # converted to one (the seams, lowering §13)
            if length(ats) >= 2 && _istobj(ats[2]) && (lb2 = _tobj_lb(ats[2]); lb2 !== nothing && _is_op(f, lb2))
                continue
            end
            csig = Tuple{ats...}
            ms = Base._methods_by_ftype(csig, -1, world)
            if !(ms isa Vector) || isempty(ms)
                push!(out, "$line: `$fname` has no method for a trait object carrying $(_traitnames(ats[findfirst(k -> k > 1 && _hastobj(ats[k]), 1:length(ats))]))")
                continue
            end
            for mm in ms
                m = mm.method
                msig = Base.unwrap_unionall(m.sig)
                params = msig.parameters
                internal_checked = false
                for k in 2:length(ats)
                    _hastobj(ats[k]) || continue
                    p = k <= length(params) ? params[k] : (isempty(params) ? Any : params[end])
                    p isa Core.TypeofVararg && (p = isdefined(p, :T) ? p.T : Any)
                    lb = _tobj_lb(p)
                    if lb === nothing && _is_trait_module_code(m) && !_is_entry(m)
                        # an internal function of a trait module (note "Internal functions need no bounds"):
                        # compiled for the trait object as part of the worker, and checked through its body
                        internal_checked || worker_problems(csig, seen, out; root = false)
                        internal_checked = true
                    elseif lb === nothing
                        if f isa Function && !isempty(traits_at(f, k - 1, length(ats) - 1))
                            push!(out, "$line: a trait object carrying $(_traitnames(ats[k])) is passed to `$fname`, whose " *
                                       "methods need other traits at argument $(k-1). Declare the bounds it needs, so the caller projects each (rule 2)")
                        elseif f === Base.getproperty || f === Base.setproperty!
                            push!(out, "$line: `t.field`: the user's data is reached only through the trait's operations")
                        else
                            push!(out, "$line: a trait object carrying $(_traitnames(ats[k])) is passed to `$fname`, an ordinary " *
                                       "function: it can do only what its traits declare. Declare `$fname` as an operation, or use the operations")
                        end
                    elseif !_is_op(f, lb)
                        # a worker called from a worker: checked too, at whatever argument types it gets
                        worker_problems(csig, seen, out; root = false)
                    end
                end
            end
        end
    end
    return out
end

"Whether a trait the trait object type `T` carries declares field `f`, writable if `write`."
function _declares_field(@nospecialize(T), f::Symbol, write::Bool)
    T = Base.unwrap_unionall(T)
    T isa DataType && T <: TObj || return false
    Xs = T.parameters[1]
    for X in (Xs isa TypeVar ? Base.uniontypes(Xs.lb) : Base.uniontypes(Xs))
        X = _family(X)
        is_trait(X) || continue
        for (g, w) in trait_fields(X)
            g === f && (!write || w) && return true
        end
    end
    return false
end

"""
Whether a call keeps its trait objects as values: `Dynamic{X}(t)`, `Compiled{X}(t)`,
`convert` to either, storing into a container of such values or of `Kept{X}` (a trait's name),
into a field declared so, or constructing a struct whose fields at the trait objects' positions
are declared so. The conversion checks the trait.
"""
function _keeps_dynamic(@nospecialize(f), ats::Vector{Any}, ex::Expr, src, sptypes)
    isdyn(@nospecialize(T)) = T isa Type && T !== Union{} && T <: HeldValue
    f isa Type && isdyn(f) && return true
    f === with_dynamic && return true                     # a `Dynamic` trait object holds the user's object
    if f === Base.convert && length(ats) == 3
        A = ats[2]
        return A isa DataType && A <: Type && isdyn(A.parameters[1])
    end
    if (f === Base.push! || f === Base.pushfirst! || f === Base.setindex! || f === Base.insert!) && length(ats) >= 3
        C = ats[2]
        return C isa Type && C <: AbstractArray && isdyn(eltype(C))
    end
    if (f === Base.setproperty! || f === Core.setfield!) && length(ats) == 4
        S = ats[2]
        nm = _CC.argextype(ex.args[3], src, sptypes)
        nm isa _CC.Const || return false
        k = nm.val
        return S isa DataType && (k isa Symbol || k isa Int) && hasfield(S, k isa Symbol ? k : fieldname(S, k)) &&
               isdyn(fieldtype(S, k))
    end
    if f isa DataType && isstructtype(f) && fieldcount(f) == length(ats) - 1
        for k in 2:length(ats)
            _hastobj(ats[k]) && !isdyn(fieldtype(f, k - 1)) && return false
        end
        return true
    end
    return false
end

"""
    checked_call(f, args...)

How an entry calls a worker. A generated function: each call signature gets
its own flag, embedded in its compiled code, so the check runs once per
signature, and the flag is saved with whichever package image compiled that
signature (rule 4 places it). The call to the worker is static.
"""
function _checked_call_body(@nospecialize(f), argtypes, argsyms)
    flag = Ref(false)
    sig = Tuple{f,argtypes...}
    return quote
        Base.@_inline_meta
        # a dynamic call: the check's reflection stays out of compiled code (and out of trimmed binaries)
        $(flag)[] || CLOSED_WORLD[] || Base.inferencebarrier(_latest)(_check_once, $flag, $sig)
        # a result like the input goes on to the entry, which inverts it
        $(_worker_call(:f, argsyms))
    end
end
"The entry's call of the worker: an ordinary call; Julia compiles the worker by facts (a trait module's method)."
_worker_call(f, argsyms) = :(return _checked_out($f($(argsyms...))))
"Whether this process builds a closed world (`--trim`)."
_closed_build() = Base.JLOptions().trim != 0
@generated checked_call(f, args...) = _checked_call_body(f, args, [:(args[$i]) for i in 1:length(args)])
# fixed arities: a call from an untyped entry dispatches on these through Julia's fast cache
# (a varargs method makes every dynamic call build its argument tuple type)
for n in 1:8
    as = [Symbol(:a, i) for i in 1:n]
    @eval @generated checked_call(f, $(as...)) = _checked_call_body(f, Any[$(as...)], $(as))
end

"""
    checked_kwcall(nt, f, args...)

`checked_call` for a function with keyword arguments: the supplied keywords,
bounded ones already projected, go to the worker's own keyword sorter, which
fills the defaults inside the trait world.
"""
@generated function checked_kwcall(nt::NamedTuple, f, args...)
    flag = Ref(false)
    sig = Tuple{typeof(Core.kwcall),nt,f,args...}
    return quote
        $(flag)[] || CLOSED_WORLD[] || Base.inferencebarrier(_latest)(_check_once, $flag, $sig)
        $(_worker_call(:(Core.kwcall), [:nt, :f, :(args...)]))
    end
end

"The worker's own signature: a keyword worker's without `Core.kwcall` and the keywords."
_worker_sig(@nospecialize(sig)) = sig.parameters[1] === typeof(Core.kwcall) ? Tuple{sig.parameters[3:end]...} : sig
"What the traits a trait object of type `T` carries declare: operations and fields, for a rule-2 message."
function _declared_text(@nospecialize(T))
    parts = String[]
    try
        U = Base.unwrap_unionall(T)
        Xs = Any[]
        if U isa DataType && U <: TObj
            V = U.parameters[2]
            if V isa DataType
                for v in V.parameters
                    v isa DataType && !isempty(v.parameters) && push!(Xs, _family(v.parameters[1]))
                end
            end
            if isempty(Xs)
                P = U.parameters[1]
                lb = P isa TypeVar ? P.lb : P
                append!(Xs, Base.uniontypes(_decode_traits(lb)))
            end
        end
        for X in unique!(Xs)
            X isa Type && is_trait(X) || continue
            ops = String[string(op) for op in _ops(X)]
            fs = String[string(f) for (f, _) in trait_fields(X)]
            push!(parts, "`$(nameof(X))` declares " * (isempty(ops) ? "no operations" : join(ops, ", ")) *
                         (isempty(fs) ? "" : "; fields " * join(fs, ", ")))
        end
    catch
    end
    return isempty(parts) ? "see its trait's declaration" : join(parts, "; ")
end

"The function a worker signature belongs to: through `Core.kwcall` for a keyword worker."
_worker_ftype(@nospecialize(sig)) = sig.parameters[1] === typeof(Core.kwcall) ? sig.parameters[3] : sig.parameters[1]

# a trait object never reaches ordinary code: one dispatch at the boundary, folded per signature
@inline _noescape(x) = x
@inline _checked_out(x) = _noescape(x)
@inline _checked_out(x::LikeResult) = x
_noescape(::Union{TObj,AbstractView,CObj,CMulti,LikeResult}) = throw(TraitUseError(["a trait object was returned to ordinary code: a trait object is a handle, not a value"]))

@machinery @noinline function _check_once(flag::Base.RefValue{Bool}, @nospecialize(sig))
    CLOSED_WORLD[] && (flag[] = true; return nothing)      # checked by verify_main at build time
    sig in _CHECKED_AHEAD[] && (flag[] = true; return nothing)   # checked while a package image was built (ahead.jl)
    _FACTS_DEBUG[] && Core.println("TraitWorld: first-call check of ", sig, ccall(:jl_generating_output, Cint, ()) == 1 ? " (while generating an image)" : "")
    # a value conforming at parameters no bound accepts: no worker for the signature
    ms = Base._methods_by_ftype(_worker_sig(sig), -1, Base.get_world_counter())::Vector
    any(m -> !_is_entry(m.method), ms) || _no_worker_error(_worker_sig(sig))
    _refuse_overrides()
    if !_def_checked(sig)                                  # checked once at its definition, at archetypes
        ps = _latest(worker_problems, sig)::Vector{String}
        isempty(ps) || throw(TraitUseError(unique(ps)))
    end
    _latest(_check_concrete, sig)
    flag[] = true
    return nothing
end
