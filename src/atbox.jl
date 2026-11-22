# The definition-time check as a reading of the method at the box (W-151; the review's P2, D-3): a method is
# bounded at a trait argument when its instance for `Dynamic{X}` is fully typed there and makes no call that
# finds no method. The instance is ordinary code at a concrete type, inferred by Julia's own inference under the
# facts rule; the check reads its record. Behind the box only the contract's operations reach the member, so a
# method that passes works, erased, for every member that will ever join.
#
# A fault is reported at the line of the checked method that passes the value, with what the call reaches.

"A call in a method's instance at the box that is not fully typed there or finds no method."
struct BoxFault
    kind::Symbol          # :nomethod (a call reaches no method), :throws (a call that only throws), :undefined (a call
                          # of a name its module does not define; `callee` is the name)
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
form of a forwarded method, a `where` variable bounded by one); a vararg of members `ts::X...` as
`Dynamic{X}, Vararg{Dynamic{X}}`, the instance a call that passes boxes there runs; a free variable is given the first of `Float64`, `Int`,
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
        for k in 1:length(vals)        # by index: Base's `zip` and `enumerate` over a `Vector{Any}` are code outside the deep class (W-167)
            w, x = vars[k], vals[k]
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
    for i in 1:length(ps)
        p = ps[i]
        for k in 1:length(vals)
            w, x = vars[k], vals[k]
            p = _substv(p, w, x)
        end
        if i > 1 && p isa Core.TypeofVararg
            # a vararg of members (`ts::X...`, traits §6.6): each element in a box, at least one: the instance a call
            # that passes boxes there runs (Julia's compilation signature for several, `Dynamic{X}, Vararg{Dynamic{X}}`)
            E = isdefined(p, :T) ? p.T : Any
            for k in 1:length(vals)
                w, x = vars[k], vals[k]
                E = _substv(E, w, x)
            end
            N = isdefined(p, :N) && p.N isa Int ? p.N : nothing
            boxed = E isa DataType && E <: Dynamic
            if !boxed
                X = _box_trait(E)
                if X !== nothing
                    Xc = _close_params(X)
                    Xc === nothing && return nothing
                    E = try Dynamic{Xc} catch; return nothing end
                    boxed = true
                end
            end
            any_box |= boxed
            boxed && N === nothing && push!(out, E)
            p = N === nothing ? Vararg{E} : Vararg{E, N}
        elseif i > 1
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
# a value at the box: a box, or a value known only by a trait; a tuple that holds one (a vararg of members, `ts`)
# passes it on
_at_box_value(@nospecialize(T)) = T isa Type && (T <: Dynamic || _trait_of(T) !== nothing || _tuple_at_box(T))
function _tuple_at_box(@nospecialize(T))
    (T isa DataType && T.name === Tuple.name) || return false
    for p in T.parameters
        Base.isvarargtype(p) && (p = Base.unwrapva(p))
        _at_box_value(p) && return true
    end
    return false
end

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
_fname(@nospecialize(fv), @nospecialize(f)) = fv isa Function ? something(_closure_form(typeof(fv)), string(nameof(fv))) :
                                                fv isa Type ? string(fv) : f isa GlobalRef ? string(f.name) : string(f)
# a closure or an anonymous function as it is written, `(t) -> …` (traits §11.3: never its generated name), or nothing;
# nothing for a named function, whose type's name is `#` and its own (its name is how a call prints it)
function _closure_form(@nospecialize(T))
    (T isa DataType && T <: Function && startswith(string(T.name.name), "#")) || return nothing
    (Base.issingletontype(T) && !startswith(string(nameof(T.instance)), "#")) && return nothing
    ms = try Base._methods_by_ftype(Tuple{T, Vararg{Any}}, 1, Base.get_world_counter()) catch; nothing end
    (ms isa Vector && length(ms) == 1) || return nothing
    w = match(r"^`([^`]*)`", _written_method(ms[1].method))
    return w === nothing ? nothing : string(w.captures[1])
end
# an argument as a call prints it (traits §11.3): a constant as written, an argument of the method by its name, else
# `::T`, its type
function _argstr(src::Core.CodeInfo, @nospecialize(a))
    a isa QuoteNode && return repr(a.value)
    (a isa Symbol || a isa Number || a isa AbstractString || a isa AbstractChar) && return repr(a)
    # the load of a global (`sum(uarea, ts)`, `uarea` not a constant here): by its name
    a isa Core.SSAValue && src.code[a.id] isa GlobalRef && return string(src.code[a.id].name)
    n = a isa Core.Argument ? a.n : a isa Core.SlotNumber ? a.id : 0
    if 1 < n <= length(src.slotnames)
        nm = string(src.slotnames[n])
        (isempty(nm) || startswith(nm, "#")) || return nm
    end
    T = _argtype(src, a)
    return something(_closure_form(T), "::" * _tstr(T))
end
# a callee that is the load of a global, `%1 = M.K` (a global not defined, or not a function), by the global's name
_callstr(src::Core.CodeInfo, @nospecialize(fv), args) = string(_fname(fv, _loaded(src, args[1])), "(", join([_argstr(src, a) for a in args[2:end]], ", "), ")")
_loaded(src::Core.CodeInfo, @nospecialize(a)) = a isa Core.SSAValue && src.code[a.id] isa GlobalRef ? src.code[a.id] : a
# a link of a chain of calls as the report names it: a function by its name, a closure as it is written, a
# keyword body (`#sum#282`, beside its function's own link) left out (""); a chain by its links, each once
function _link_name(@nospecialize(fv), @nospecialize(f))
    fv isa Function || return _fname(fv, f)
    n = string(nameof(fv))
    startswith(n, "#") || return n
    occursin(r"^#[^#]+#\d+$", n) && return ""
    return something(_closure_form(typeof(fv)), "an anonymous function")
end
_chain_names(chain) = join(unique!([c for c in chain if !isempty(c)]), " → ")

# the frames of statement `i` of an optimized instance: (method or name, file, line), outermost first
function _frames(src::Core.CodeInfo, i::Int)
    nodes = try Base.IRShow.buildLineInfoNode(src.debuginfo, nothing, i) catch; return Any[] end
    return Any[(n.method, n.file, Int(n.line)) for n in nodes]
end

# Whether the call as written, at the types the code knows, has a method: Julia's lookup at those types. A call
# left to run time is read so; and so is Julia's optimized form of a call at an abstract argument whose methods
# cover a part of it (a test of the argument's type, the method's call, and else `Core.throw_methoderror`): the
# other branch of that split is the call as written, not a call that finds no method (traits §7.3; open issue 249).
function _has_method_at(@nospecialize(tt), world::UInt)
    ms = try Base._methods_by_ftype(tt, -1, world) catch; nothing end
    return ms isa Vector && !isempty(ms)
end
# the types `Core.throw_methoderror(f, args...)` is called at: the call it stands for
_raised_call(src::Core.CodeInfo, args) = Tuple{Any[_argtype(src, a) for a in args[2:end]]...}

# a tuple of no fixed length that holds a value at the box (a vararg of members, `ts`), as one call that passes it
# runs: its fixed elements, or the vararg's one element (traits §7.3: each element in a box, at least one). Where the
# length is not fixed, Base's code over the tuple meets calls at abstract types (`Generator{I} where I<:Tuple{…}`),
# which the facts rule leaves to run time: the call that finds no method is below them
function _fixed_length(@nospecialize(T))
    (T isa DataType && T.name === Tuple.name && _tuple_at_box(T)) || return T
    ps = Any[T.parameters...]
    (!isempty(ps) && Base.isvarargtype(ps[end]) && !(isdefined(ps[end], :N) && ps[end].N isa Int)) || return T
    E = isdefined(ps[end], :T) ? ps[end].T : Any
    pop!(ps)
    isempty(ps) && push!(ps, E)
    return Tuple{ps...}
end

# The call that finds no method with a value at the box, below a call that only throws: the chain of calls down
# to it, or nothing (the call throws by itself: an undeclared field read at the box, an intended `throw`). Each
# callee is read again at the argument types of its call, a tuple of boxes of no fixed length at its fixed length.
# Followed to the call that finds no method whatever its depth: the signatures read once each (`seen`), so a
# recursion ends.
function _reaches_no_method(interp, @nospecialize(tt), seen::Set{Any})
    tt isa DataType && (tt = Tuple{Any[_fixed_length(p) for p in tt.parameters]...})
    tt in seen && return nothing
    push!(seen, tt)
    r = try Base.code_typed_by_type(tt; interp, optimize = true) catch; return nothing end
    (length(r) == 1 && r[1][1] isa Core.CodeInfo) || return nothing
    src = r[1][1]
    world = CC.get_inference_world(interp)
    for (i, st) in enumerate(src.code)
        st isa Expr && st.head === :(=) && (st = st.args[2])
        st isa Expr && st.head in (:call, :invoke) || continue
        args = st.head === :invoke ? st.args[2:end] : st.args
        fv = _callee_value(src, args[1])
        ats = Any[_argtype(src, a) for a in args[2:end]]
        if fv === Core.throw_methoderror && length(ats) >= 1
            g = _callee_value(src, args[2])
            any(_at_box_value, ats[2:end]) || continue
            _has_method_at(_raised_call(src, args), world) && continue      # a split's other branch
            return Any[string(_fname(g, args[2]), "(", join((something(_closure_form(T), "::" * _tstr(T)) for T in ats[2:end]), ", "), ")"), g]
        end
        # a call that only throws, compiled (`invoke`) or left to run time with its result inferred as `Union{}`
        if src.ssavaluetypes[i] === Union{} && any(_at_box_value, ats)
            below = _reaches_no_method(interp, Tuple{_argtype(src, args[1]), ats...}, seen)
            below === nothing || return pushfirst!(below, _link_name(fv, args[1]))
        end
    end
    return nothing
end

# the compiler's interpreter of the facts mode, made where a run-time site reaches it: its constructor is code
# outside the deep class (W-167)
_facts_interp(world::UInt) = CC.NativeInterpreter(world; facts = true)

"""
    check_at_box(m::Method; world) -> Vector{BoxFault} or nothing

The method read at the box (D-3): its instance at `box_signature(m)`, inferred under the method's policy,
optimized, and kept in Julia's cache with its edges (an image keeps it; a definition that changes it ends it);
inferred apart only where the cache keeps no code.
A fault is a call in it that takes a value at the box (the box, or a value known only by a trait) and finds no
method (directly, below a call that only throws, or left to run time with no method at the types known), or only
throws (an undeclared field read at the box), or calls a name `m`'s module does not define. A call left to run time that finds a method when it runs is Julia's
barrier, no fault. A call is read as written, at the types the code knows: where the optimizer splits a call at an
abstract argument into the method's call and, for the rest of the argument's type, `Core.throw_methoderror`, that
other branch is no fault where a method applies at those types. Each is reported at the line of `m` that passes the
value. `nothing` where `m` has no argument at a trait or the box cannot be formed.
"""
function check_at_box(m::Method; world::UInt = Base.get_world_counter())
    sig = box_signature(m)
    sig === nothing && return nothing
    # the chain below a call that only throws is read by the facts rule, as each callee is compiled
    interp = _runtime_site(_facts_interp, world)
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
    return _box_faults(m, src, interp, world)
end

# The faults of `m`'s code at the box, `src` (its optimized instance; a probe may pass another reading of it)
function _box_faults(m::Method, src::Core.CodeInfo, interp, world::UInt)
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
        # a call of a name its module does not define, with a value at the box: at the module's end a fault (traits
        # §7.3, "When"); before it, the method waits for the name (`_decide_bounded`)
        # (the callee, or a function passed on: `sum(uarea, ts)`)
        undef = false
        for a in args
            name = _undefined_callee(src, a, m.module)
            (name === nothing || !any(_at_box_value, ats)) && continue
            push!(faults, BoxFault(:undefined, string(_callstr(src, fv, args), ": `", name, "` is not defined in ", m.module,
                                                      _undefined_hint(m, name), via), m, line, name))
            undef = true
        end
        undef && continue
        if fv === Core.throw_methoderror
            length(ats) >= 2 && any(_at_box_value, ats[2:end]) || continue
            # the other branch of a split: the call as written has a method at the types the code knows
            _has_method_at(_raised_call(src, args), world) && continue
            g = _callee_value(src, args[2])
            push!(faults, BoxFault(:nomethod, string(_callstr(src, g, args[2:end]), " has no method", via), m, line, g))
            continue
        end
        (fv isa Core.Builtin || fv isa Core.IntrinsicFunction || fv === Base.kwerr) && continue
        any(_at_box_value, ats) || continue
        if st.head === :invoke || src.ssavaluetypes[i] === Union{}
            # a call that only throws: what it reaches where a call below finds no method. A call left to run time
            # whose result inference gives as `Union{}` (at a vararg of boxes, a tuple of no fixed length) is one too
            src.ssavaluetypes[i] === Union{} || continue
            chain = _reaches_no_method(interp, Tuple{_argtype(src, f), ats...}, Set{Any}())
            call = _callstr(src, fv, args)
            if chain === nothing
                what = (fv === getproperty || fv === setproperty! || fv === _not_declared) && length(args) >= 3 && args[3] isa QuoteNode ?
                    string("the field `", args[3].value, "` is no declared field of ", _box_trait_of(ats[1])) :
                    fv === _declared_const && length(args) >= 3 && args[3] isa QuoteNode ?
                    string("the field `", args[3].value, "` is declared @const by ", _box_trait_of(ats[1])) :
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

# The name a call's callee loads where it is a global of the module `M` that is not defined (a call `nothere(a)`, its
# callee the load `M.nothere`), else nothing. A name of another module, written `N.name`, is not one: `M`'s end does
# not decide it.
function _undefined_callee(src::Core.CodeInfo, @nospecialize(f), M::Module)
    f isa Core.SSAValue && (f = src.code[f.id])
    (f isa GlobalRef && f.mod === M && !isdefined(M, f.name)) || return nothing
    return f.name
end
# where the undefined name is an operation of a trait the method is at (an operation not imported): where to import it
function _undefined_hint(m::Method, name::Symbol)
    for X in _argument_traits(m), (c, _) in _contracts_of(X), op in c.operations
        op.name === name && op.f isa Function && parentmodule(op.f) !== m.module || continue
        M = parentmodule(op.f)
        return string("; `", name, "` is an operation of ", bare(c.trait), ": `using ", M, ": ", name, "` imports it")
    end
    return ""
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
    src = inf isa Core.CodeInfo ? _runtime_site(copy, inf)::Core.CodeInfo : inf isa String ? (try Base._uncompressed_ir(ci, inf) catch; nothing end) : nothing
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
        Base.isvarargtype(p) && (p = Base.unwrapva(p))      # a vararg of members: its element (traits §7.3)
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
    n = Int(m.nargs)
    boxed = String[]
    va_named = false
    if sig isa DataType && written isa DataType
        for (i, p) in enumerate(sig.parameters)
            P = p isa Core.TypeofVararg ? (isdefined(p, :T) ? p.T : Any) : p
            i > 1 && P isa DataType && P <: Dynamic && !(i <= length(written.parameters) && written.parameters[i] == p) || continue
            # the positions of a vararg of members (from the method's last argument on): each of its elements in a box
            each = m.isva && i >= n
            if each
                va_named && continue
                va_named = true
            end
            nm = min(i, n) <= length(names) ? string(names[min(i, n)]) : ""
            who = isempty(nm) || startswith(nm, "#") ? (each ? "each of the arguments from $(n - 1)" : "the argument $(i - 1)") :
                  each ? "each of `$nm`" : "`$nm`"
            push!(boxed, string(who, " in a box, `", _tstr(P), "`"))
        end
    end
    read = isempty(boxed) ? "read at the box" : "read with " * join(boxed, ", and ")
    return string(_written_method(m), " is declared bounded, and is not bounded: ", read)
end
