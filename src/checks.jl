# ---------------------------------------------------------------------------
# What library code may do with a trait object (rule 3 and the "may do"
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

"Whether `f` is an operation function of one of the traits in `lb` (its methods on trait objects forward)."
function _is_op(@nospecialize(f), @nospecialize(lb))
    for X in Base.uniontypes(lb)
        is_trait(X) || continue
        for op in _ops(X)
            _opfn(X, op) === f && return true
        end
    end
    return false
end

_traitnames(@nospecialize(T)) = _istobj(T) ? join(string.(Base.uniontypes(T.parameters[1])), ", ") : string(T)

"""
    worker_problems(sig) -> Vector{String}

Problems in the worker selected by the concrete call signature `sig`, and in
the workers it calls.
"""
function worker_problems(@nospecialize(sig), seen = Base.IdSet{Any}(), out = String[])
    sig in seen && return out
    push!(seen, sig)
    world = Base.get_world_counter()
    for (src, _) in Base.code_typed_by_type(sig; optimize = false, world)
        mi = src.parent
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
            if !any(k -> _hastobj(ats[k]), 2:length(ats))
                _layering!(out, seen, f, ats, src, mi, i, world)
                continue
            end
            line = _line_of(src, mi, i)
            if f === nothing
                push!(out, "$line: a trait object is passed to a function not known at compile time")
                continue
            end
            fname = f isa Function ? nameof(f) : f
            f === Core._typeof_captured_variable && continue      # closure lowering: the closure body is checked at its `new`
            if f isa Core.Builtin || f isa Core.IntrinsicFunction
                what = f === Core.getfield ? "`t.field`: the user's data is reached only through the trait's operations" :
                       f === Core.typeof ? "`typeof(t)`: code must not depend on the user's type" :
                       f === Core.tuple ? "stored in a tuple: a trait object is a handle, not a value" :
                       f === Core._apply_iterate ? "splatted into a call" :
                       "passed to the builtin `$fname`"
                push!(out, "$line: $what")
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
                for k in 2:length(ats)
                    _hastobj(ats[k]) || continue
                    p = k <= length(params) ? params[k] : (isempty(params) ? Any : params[end])
                    p isa Core.TypeofVararg && (p = isdefined(p, :T) ? p.T : Any)
                    lb = _tobj_lb(p)
                    if lb === nothing
                        if f isa Function && !isempty(traits_at(f, k - 1, length(ats) - 1))
                            push!(out, "$line: a trait object carrying $(_traitnames(ats[k])) is passed to `$fname`, whose " *
                                       "methods need other traits at argument $(k-1). Declare the bounds it needs, so the caller projects each (rule 3)")
                        elseif f === Base.getproperty || f === Base.setproperty!
                            push!(out, "$line: `t.field`: the user's data is reached only through the trait's operations")
                        else
                            push!(out, "$line: a trait object carrying $(_traitnames(ats[k])) is passed to `$fname`, an ordinary " *
                                       "function: it can do only what its traits declare. Declare `$fname` as an operation, or use the operations")
                        end
                    elseif !_is_op(f, lb) && all(T -> isconcretetype(T), ats)
                        worker_problems(csig, seen, out)
                    end
                end
            end
        end
    end
    return out
end

"""
Rule 1 on typed code: a call that resolves to a method outside the trait
world (a package the module never imported, reached as `Main.Plain.f()`) is
reported; calls into helpers of trait modules are followed.
"""
function _layering!(out, seen, @nospecialize(f), ats, src, mi, i, world)
    (f === nothing || f isa Core.Builtin || f isa Core.IntrinsicFunction) && return nothing
    csig = Tuple{ats...}
    ms = Base._methods_by_ftype(csig, -1, world)
    ms isa Vector || return nothing
    for mm in ms
        m = mm.method
        if !is_trait_world(m.module)
            push!(out, "$(_line_of(src, mi, i)): calls $(m.module).$(m.name), outside the trait world (rule 1): " *
                       "the trait world uses only itself")
        elseif owner(Base.moduleroot(m.module)) !== :Julia && Base.moduleroot(m.module) !== TraitWorld &&
               all(isconcretetype, ats)
            worker_problems(csig, seen, out)
        end
    end
    return nothing
end

"""
    checked_call(f, args...)

How an entry calls a worker. A generated function: each call signature gets
its own flag, embedded in its compiled code, so the check runs once per
signature, and the flag is saved with whichever package image compiled that
signature (rule 7 places it). The call to the worker is static.
"""
@generated function checked_call(f, args...)
    flag = Ref(false)
    guard = GuardState()
    sig = Tuple{f,args...}
    return quote
        # a dynamic call: the check's reflection stays out of compiled code (and out of trimmed binaries)
        $(flag)[] || CLOSED_WORLD[] || Base.inferencebarrier(_check_once)($flag, $sig)
        _guard($guard, $sig)
        return f(args...)
    end
end

@noinline function _check_once(flag::Base.RefValue{Bool}, @nospecialize(sig))
    CLOSED_WORLD[] && (flag[] = true; return nothing)      # checked by verify_main at build time
    ps = Base.invokelatest(worker_problems, sig)::Vector{String}
    isempty(ps) || throw(TraitUseError(unique(ps)))
    Base.invokelatest(_check_concrete, sig)
    flag[] = true
    return nothing
end
