# The definition-time check as a reading of the method at the box (W-151; the review's P2, D-3): a method is
# bounded at a trait argument when its instance for `Dynamic{X}` is fully typed there and makes no call that
# finds no method. The instance is ordinary code at a concrete type, inferred by Julia's own inference under the
# facts rule; the check reads its record. Behind the box only the contract's operations reach the member, so a
# method that passes works, erased, for every member that will ever join.
#
# A fault is reported at the line of the checked method that passes the value, with what the call reaches.

"A call in a method's instance at the box that is not fully typed there or finds no method."
struct BoxFault
    kind::Symbol          # :nomethod (a call reaches no method), :throws (a call that only throws)
    what::String          # the call, and what it reaches
    method::Method        # the method checked
    line::Int             # the line in `method` that passes the value
    callee::Any           # the function that has no method (at the end of the chain), or the function called
end

# the box's type parameter for a declared argument type, or nothing where the argument is not at a trait:
# a trait or an intersection; a kept-form union `Union{Dynamic{<:X}, Compiled{<:X}}` (a forwarded method)
function _box_trait(@nospecialize(p))
    p isa TypeVar && (p = p.ub)
    if p isa Union
        for c in Base.uniontypes(p)
            u = Base.unwrap_unionall(c)
            if u isa DataType && u.name === Base.unwrap_unionall(Dynamic).name && c isa UnionAll
                return c.var.ub
            end
        end
        return nothing
    end
    return _trait_of(p)
end

# a free variable's stand-in: the first of a few common concrete types its bounds allow
const _STAND_INS = (Float64, Int, Symbol, String)
function _stand_in(v::TypeVar, @nospecialize(ub))
    for T in _STAND_INS
        (v.lb <: T && T <: ub) && return T
    end
    return ub isa Type && isconcretetype(ub) ? ub : nothing
end
# a trait with open parameters, closed at a stand-in where its bounds allow (the reading needs a concrete box)
function _close_params(@nospecialize(X))
    while X isa UnionAll
        T = _stand_in(X.var, X.var.ub)
        T === nothing && return nothing
        X = X{T}
    end
    return X
end
_substv(@nospecialize(t), v::TypeVar, @nospecialize(x)) =
    t === v ? x : t isa Core.TypeofVararg ? t : (try (UnionAll(v, t)){x} catch; t end)

"""
    box_signature(m::Method) -> Type or nothing

`m`'s signature with `Dynamic{X}` in place of each argument at a trait `X` (a trait, an intersection, a kept
form of a forwarded method, a `where` variable bounded by one); a free variable is given the first of `Float64`, `Int`,
`Symbol`, `String` its bounds allow, else its bound where that is concrete. `nothing` where no argument is at a trait, or the box cannot be formed.
"""
function box_signature(m::Method)
    sig = m.sig
    vars = TypeVar[]
    while sig isa UnionAll
        push!(vars, sig.var)
        sig = sig.body
    end
    ps = collect(sig.parameters)
    vals = Any[]
    for v in vars
        ub = v.ub
        for (w, x) in zip(vars, vals)
            ub = ub isa Type || ub isa TypeVar ? _substv(ub, w, x) : ub
        end
        X = _box_trait(ub)
        val = if X !== nothing
            Xc = _close_params(X)
            Xc === nothing && return nothing
            try Dynamic{Xc} catch; return nothing end
        else
            T = _stand_in(v, ub)
            T === nothing && return nothing
            T
        end
        push!(vals, val)
    end
    out = Any[]
    any_box = false
    for (i, p) in enumerate(ps)
        for (w, x) in zip(vars, vals)
            p = _substv(p, w, x)
        end
        if i > 1 && !(p isa Core.TypeofVararg)
            if p isa DataType && p <: Dynamic
                any_box = true
            else
                X = _box_trait(p)
                if X !== nothing
                    Xc = _close_params(X)
                    Xc === nothing && return nothing
                    p = try Dynamic{Xc} catch; return nothing end
                    any_box = true
                end
            end
        end
        push!(out, p)
    end
    any_box || return nothing
    return try Tuple{out...} catch; nothing end
end

_box_trait_of(@nospecialize(T)) = T isa DataType && T <: Dynamic ? T.parameters[1] : T
# a value at the box: a box, or a value known only by a trait
_at_box_value(@nospecialize(T)) = T isa Type && (T <: Dynamic || _trait_of(T) !== nothing)

function _argtype(src::Core.CodeInfo, @nospecialize(a))
    a isa Core.SSAValue && return CC.widenconst(src.ssavaluetypes[a.id])
    a isa Core.Argument && return CC.widenconst(src.slottypes[a.n])
    a isa Core.SlotNumber && return CC.widenconst(src.slottypes[a.id])
    a isa GlobalRef && return isdefined(a.mod, a.name) && isconst(a.mod, a.name) ? Core.Typeof(getglobal(a.mod, a.name)) : Any
    a isa QuoteNode && return Core.Typeof(a.value)
    a isa Expr && return Any
    return Core.Typeof(a)
end
function _callee_value(src::Core.CodeInfo, @nospecialize(f))
    f isa GlobalRef && return isdefined(f.mod, f.name) && isconst(f.mod, f.name) ? getglobal(f.mod, f.name) : nothing
    f isa QuoteNode && return f.value
    if f isa Core.SSAValue || f isa Core.Argument
        T = _argtype(src, f)
        return Base.issingletontype(T) ? T.instance : nothing
    end
    return f
end
_fname(@nospecialize(fv), @nospecialize(f)) = fv isa Function ? string(nameof(fv)) : fv isa Type ? string(fv) : string(f)
# an argument as a call prints it (traits §11.3): a constant as written, an argument of the method by its name, else
# `::T`, its type
function _argstr(src::Core.CodeInfo, @nospecialize(a))
    a isa QuoteNode && return repr(a.value)
    (a isa Symbol || a isa Number || a isa AbstractString || a isa AbstractChar) && return repr(a)
    n = a isa Core.Argument ? a.n : a isa Core.SlotNumber ? a.id : 0
    if 1 < n <= length(src.slotnames)
        nm = string(src.slotnames[n])
        (isempty(nm) || startswith(nm, "#")) || return nm
    end
    return "::" * _tstr(_argtype(src, a))
end
_callstr(src::Core.CodeInfo, @nospecialize(fv), args) = string(_fname(fv, args[1]), "(", join([_argstr(src, a) for a in args[2:end]], ", "), ")")
# a chain of calls by the functions' names, the keyword bodies (`#sum#282`) left out
_chain_names(chain) = join(unique!([c for c in chain if !startswith(c, "#")]), " → ")

# the frames of statement `i` of an optimized instance: (method or name, file, line), outermost first
function _frames(src::Core.CodeInfo, i::Int)
    nodes = try Base.IRShow.buildLineInfoNode(src.debuginfo, nothing, i) catch; return Any[] end
    return Any[(n.method, n.file, Int(n.line)) for n in nodes]
end

# The call that finds no method with a value at the box, below a call that only throws: the chain of calls down
# to it, or nothing (the call throws by itself: an undeclared field read at the box, an intended `throw`). Each
# callee is read again at the argument types of its call.
function _reaches_no_method(interp, @nospecialize(tt), depth::Int, seen::Set{Any})
    depth > 20 && return nothing
    tt in seen && return nothing
    push!(seen, tt)
    r = try Base.code_typed_by_type(tt; interp, optimize = true) catch; return nothing end
    (length(r) == 1 && r[1][1] isa Core.CodeInfo) || return nothing
    src = r[1][1]
    for (i, st) in enumerate(src.code)
        st isa Expr && st.head === :(=) && (st = st.args[2])
        st isa Expr && st.head in (:call, :invoke) || continue
        args = st.head === :invoke ? st.args[2:end] : st.args
        fv = _callee_value(src, args[1])
        ats = Any[_argtype(src, a) for a in args[2:end]]
        if fv === Core.throw_methoderror && length(ats) >= 1
            g = _callee_value(src, args[2])
            any(_at_box_value, ats[2:end]) || continue
            return Any[string(_fname(g, args[2]), "(", join(("::" * _tstr(T) for T in ats[2:end]), ", "), ")"), g]
        end
        if st.head === :invoke && src.ssavaluetypes[i] === Union{} && any(_at_box_value, ats)
            below = _reaches_no_method(interp, Tuple{_argtype(src, args[1]), ats...}, depth + 1, seen)
            below === nothing || return pushfirst!(below, _fname(fv, args[1]))
        end
    end
    return nothing
end

"""
    check_at_box(m::Method; world) -> Vector{BoxFault} or nothing

The method read at the box (D-3): its instance at `box_signature(m)`, inferred under the method's policy,
optimized, and kept in Julia's cache with its edges (an image keeps it; a definition that changes it ends it);
inferred apart only where the cache keeps no code.
A fault is a call in it that takes a value at the box (the box, or a value known only by a trait) and finds no
method (directly, below a call that only throws, or left to run time with no method at the types known), or only
throws (an undeclared field read at the box). A call left to run time that finds a method when it runs is Julia's
barrier, no fault. Each is reported at the line of `m` that passes the value. `nothing` where `m` has no argument
at a trait or the box cannot be formed.
"""
function check_at_box(m::Method; world::UInt = Base.get_world_counter())
    sig = box_signature(m)
    sig === nothing && return nothing
    # the chain below a call that only throws is read by the facts rule, as each callee is compiled
    interp = CC.NativeInterpreter(world; facts = true)
    src = _box_instance(sig, world)
    if src === nothing
        # the native interpreter runs in inference's own world (Base's reflection): no package's method ends the
        # compiler's code it runs
        r = try
            Base.code_typed_by_type(sig; interp, optimize = true)
        catch
            return nothing
        end
        (length(r) == 1 && r[1][1] isa Core.CodeInfo) || return nothing
        src = r[1][1]
    end
    faults = BoxFault[]
    for (i, st) in enumerate(src.code)
        st isa Expr && st.head === :(=) && (st = st.args[2])
        st isa Expr && st.head in (:call, :invoke) || continue
        args = st.head === :invoke ? st.args[2:end] : st.args
        f = args[1]
        fv = _callee_value(src, f)
        ats = Any[_argtype(src, a) for a in args[2:end]]
        frames = _frames(src, i)
        line = isempty(frames) ? Int(m.line) : frames[1][3]
        via = length(frames) > 1 ? string(" (in ", frames[end][1], " at ", basename(string(frames[end][2])), ":", frames[end][3], ")") : ""
        if fv === Core.throw_methoderror
            length(ats) >= 2 && any(_at_box_value, ats[2:end]) || continue
            g = _callee_value(src, args[2])
            push!(faults, BoxFault(:nomethod, string(_callstr(src, g, args[2:end]), " has no method", via), m, line, g))
            continue
        end
        (fv isa Core.Builtin || fv isa Core.IntrinsicFunction || fv === Base.kwerr) && continue
        any(_at_box_value, ats) || continue
        if st.head === :invoke
            # a call that only throws: what it reaches where a call below finds no method
            src.ssavaluetypes[i] === Union{} || continue
            chain = _reaches_no_method(interp, Tuple{_argtype(src, f), ats...}, 1, Set{Any}())
            call = _callstr(src, fv, args)
            if chain === nothing
                what = (fv === getproperty || fv === setproperty!) && length(args) >= 3 && args[3] isa QuoteNode ?
                    string("the field `", args[3].value, "` is no declared field of ", _box_trait_of(ats[1])) :
                    string(call, " only throws")
                push!(faults, BoxFault(:throws, string(what, via), m, line, fv))
            else
                through = _chain_names(chain[1:end-2])
                push!(faults, BoxFault(:nomethod, string(call, " reaches ", chain[end-1], ", which has no method",
                                                          isempty(through) ? "" : string(" (through ", through, ")"), via),
                                       m, line, chain[end]))
            end
            continue
        end
        # a call left to run time (an argument of a type the code does not know, a callee not settled by the facts
        # rule): Julia's barrier, which finds a method when it runs. A fault only where no method applies at the
        # types known here
        ms = try Base._methods_by_ftype(Tuple{_argtype(src, f), ats...}, -1, world) catch; nothing end
        if ms isa Vector && isempty(ms)
            push!(faults, BoxFault(:nomethod, string(_callstr(src, fv, args), " has no method", via), m, line, fv))
        end
    end
    return faults
end

# The method's instance at the box (compiler §6.7, D-3): the instance a box's call runs, inferred and optimized by
# Julia's own inference under the method's policy and cached with its edges, so that an image keeps it as code and a
# later definition ends it as it ends any code. Run in the world Julia's inference runs in, as the classification
# was. Its optimized code, or nothing where the cache keeps none, or where a box's call runs an instance at another
# signature: the check then reads the box apart.
function _box_instance(@nospecialize(sig), world::UInt)
    mi = try
        Base.method_instance(sig; world)
    catch
        nothing
    end
    mi isa Core.MethodInstance || return nothing
    mi.specTypes == sig || return nothing
    ci = try
        Base.invoke_in_typeinf_world(CC.typeinf_ext_toplevel, mi, world, CC.SOURCE_MODE_GET_SOURCE, CC.TRIM_NO)
    catch
        nothing
    end
    ci isa Core.CodeInstance || return nothing
    inf = ci.inferred
    src = inf isa Core.CodeInfo ? copy(inf) : inf isa String ? (try Base._uncompressed_ir(ci, inf) catch; nothing end) : nothing
    src isa Core.CodeInfo || return nothing
    if src.slottypes === nothing
        # the cache keeps no slot types: the arguments' types are the instance's, a varargs tail as its tuple
        m = mi.def::Method
        ps = Any[(Base.unwrap_unionall(mi.specTypes)::DataType).parameters...]
        n = Int(m.nargs)
        if m.isva
            ps = Any[ps[1:n-1]..., Tuple{ps[n:end]...}]
        end
        src.slottypes = Any[ps[1:min(n, length(ps))]...]
    end
    return src
end

# whether a method is checked at the box: an argument at a trait, or a kept form of a forwarded method; not a trait's own
# method for an operation, not a forwarder
function _at_box_checked(m::Method)
    _is_trait_method(m) && return false
    sig = Base.unwrap_unionall(m.sig)
    sig isa DataType || return false
    # a keyword method's sorter: its body's method is read instead, with the keywords as declared
    sig.parameters[1] === typeof(Core.kwcall) && return false
    for p in sig.parameters[2:end]
        Base.isvarargtype(p) && continue
        _box_trait(p) === nothing || return !_is_forwarder(m)
    end
    return false
end

_fault_line(u::BoxFault) = "$(u.what), at line $(u.line)"

# The head of the bounded check's refusal (traits §7.3, §11.3): the method as its signature is written, and each
# argument read in a box, by its name, with the box's type: never the compiler's tuple type
function _bounded_head(m::Method)
    sig = box_signature(m)
    written = Base.unwrap_unionall(m.sig)
    names = Base.method_argnames(m)
    boxed = String[]
    if sig isa DataType && written isa DataType
        for (i, p) in enumerate(sig.parameters)
            i > 1 && p isa DataType && p <: Dynamic && !(i <= length(written.parameters) && written.parameters[i] == p) || continue
            nm = i <= length(names) ? string(names[i]) : ""
            push!(boxed, string(isempty(nm) || startswith(nm, "#") ? "the argument $(i - 1)" : "`$nm`", " in a box, `", _tstr(p), "`"))
        end
    end
    read = isempty(boxed) ? "read at the box" : "read with " * join(boxed, ", and ")
    return string(_written_method(m), " is declared bounded, and is not bounded: ", read)
end
