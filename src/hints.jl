# Hints on Julia's `MethodError` where a trait is involved (traits §11.4; lowering §11): a value that
# is not a member, a member at other parameter values, a broken shared variable, a call of an
# operation outside its declared signature. An ambiguity between two traits: Julia's own message names
# the joint method to define, `f(::All{X, Y})`.

function _method_error_hint(io::IO, ex::MethodError, @nospecialize(argtypes), @nospecialize(kwargs))
    lines = String[]
    try
        _trait_hints!(lines, ex.f, ex.args, ex.world)
        _positional_hint!(lines, ex.f, ex.args)
    catch
        return
    end
    for l in unique!(lines)
        print(io, "\n")
        printstyled(io, "Hint: "; bold = true)
        print(io, l)
    end
end

# the trait an argument is declared with: a trait's instance (`X`, `X{P}`, `X{T}` with `T` a where variable)
function _declared_trait(@nospecialize(d))
    d isa TypeVar && (d = d.ub)
    istrait(d) || return nothing
    contract(d) === nothing && return nothing
    return d
end

# the trait's instance at a member type: its parameters' values there (traits §3.2)
function _instance_at(@nospecialize(X), @nospecialize(T))
    T isa Type && T <: bare(X) || return nothing
    inst = try first(check_member(bare(X), T)) catch; nothing end
    return inst
end

"The set's declared members (its candidates, compiler §7.2), in declaration order."
members_of(@nospecialize(X)) = collect(Any, ccall(:jl_candidates_of, Any, (Any,), bare(X)))
_members_of(@nospecialize(X)) = members_of(X)

function _trait_hints!(lines, @nospecialize(f), args, world::UInt)
    n = length(args)
    ms = try methods(f) catch; return end
    seen_ops = Set{Any}()
    for m in ms
        sig = Base.unwrap_unionall(m.sig)
        sig isa DataType || continue
        # an operation that is another owner's function (Base's `getindex`, for BaseTraits' `Indexable`):
        # a failed call of it says nothing of the trait, so the trait's own method gives no hint
        _is_trait_method(m) && (try owner(parentmodule(f)) != owner(m.module) catch; false end) && continue
        ps = sig.parameters
        # a call of an operation: its declared signature
        for i in 2:length(ps)
            X = _declared_trait(ps[i])
            X === nothing && continue
            c = contract(X)
            for op in c.operations
                (op.f === f && !(op in seen_ops)) || continue
                push!(seen_ops, op)
                push!(lines, "`$(op.name)` is declared `$(_declared(op, c))` by $(_tstr(bare(X)))")
            end
        end
        (m.isva ? n >= length(ps) - 2 : n == length(ps) - 1) || continue
        names = Base.method_argnames(m)
        shared = Dict{TypeVar,Vector{Tuple{Symbol,Any}}}()
        for i in 1:min(n, length(ps) - 1)
            d = ps[i + 1]
            Base.isvarargtype(d) && break
            v = args[i]
            _callable_hint!(lines, d, v)
            X = _declared_trait(d)
            X === nothing && continue
            T = typeof(v)
            nm = i + 1 <= length(names) ? names[i + 1] : Symbol("#", i)
            # where variables shared between trait arguments: each argument's value of them
            dd = Base.unwrap_unionall(d isa TypeVar ? d.ub : d)
            inst = _instance_at(X, T)
            if dd isa DataType && inst isa DataType
                for (k, p) in enumerate(dd.parameters)
                    p isa TypeVar && k <= length(inst.parameters) &&
                        push!(get!(Vector{Tuple{Symbol,Any}}, shared, p), (nm, inst.parameters[k]))
                end
            end
            dtest = d isa TypeVar ? d.ub : d
            free = Base.has_free_typevars(dtest)
            # with a where variable, a member at any value of it passes here (the shared-variable hint below)
            (free ? v isa bare(X) : v isa dtest) && continue
            if inst !== nothing
                free || push!(lines, "`$nm` is a member of `$(_tstr(inst))`; the method takes `$(_tstr(d))`")
            else
                mem = _members_of(X)
                few = 1 <= length(mem) <= 5 ? " (its declared members: " * join(map(_tstr, mem), ", ") * ")" : ""
                push!(lines, "`$(_tstr(T))` is not a member of `$(_tstr(bare(X)))`$few; `@implement $(_tstr(bare(X))) $(_tstr(T))` declares it")
            end
        end
        for (tv, uses) in shared
            vals = unique(last.(uses))
            length(vals) > 1 || continue
            push!(lines, "`$(tv.name)` is " * join(["`$(u[2])` for `$(u[1])`" for u in uses], " and "))
        end
    end
    return lines
end

# a function that is not a member of the Callable{A, S} a method takes: its methods (lowering §9)
function _callable_hint!(lines, @nospecialize(d), @nospecialize(v))
    dd = Base.unwrap_unionall(d isa TypeVar ? d.ub : d)
    (dd isa DataType && dd.name === Base.unwrap_unionall(Core.Callable).name) || return
    v isa (d isa TypeVar ? d.ub : d) && return
    A = dd.parameters[1]
    A isa Type || return
    ms = try collect(methods(v)) catch; Method[] end
    sigs = String[]
    for m in first(ms, 3)
        sig = Base.unwrap_unionall(m.sig)
        sig isa DataType || continue
        push!(sigs, "(" * join(("::" * _tstr(t) for t in sig.parameters[2:end]), ", ") * ")")
    end
    name = v isa Function ? string(nameof(v)) : _tstr(typeof(v))
    push!(lines, "`$name` is not a `$(replace(_tstr(d), "Core.Callable" => "Callable"))`: none of its methods takes `$(_tstr(A))`" *
                 (isempty(sigs) ? "" : "; its methods take " * join(sigs, ", ") * (length(ms) > 3 ? ", …" : "")))
end
