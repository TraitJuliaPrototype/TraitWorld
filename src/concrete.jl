# ---------------------------------------------------------------------------
# Concrete mode, ported from TraitRegions: an opt-in contract that a trait
# module's code works on concrete types only.
#
#     @warn_on_abstract @trait_module begin … end        # a whole trait module
#     @error_on_abstract f(t::ColTable, i::Int) = …      # one function, inside a trait module
#
# The check runs once per worker signature, in `checked_call`'s first call,
# so its result is saved with whichever package image compiled the signature
# (the trait module, a conformer, an application). It walks the optimized
# code of the worker and of every function of the trait module's own package
# it calls on a normal path, reports each use of an abstract value, and traces
# it to its root cause, through any number of packages: a field declared with
# an abstract type, a boxed variable, a variable whose type changes, a
# non-constant global, an abstract declared result. Workers see only deeply
# concrete representations and operation results asserted to their declared
# types, so an abstract value can only come from the module's own code or the
# code it calls.
# ---------------------------------------------------------------------------

struct AbstractFinding
    line::String            # where the abstract value is used, in the region's code
    use::String             # what uses it: "+(::Int64, ::Any)", "returns ::Any", ...
    inloop::Bool
    origin::Vector{String}  # from the use to the root cause (last)
end

"""
    AbstractTypeError

Raised by an `@error_on_abstract` function whose code, at the representations
it is called with, uses abstract types on a normal path.
"""
struct AbstractTypeError <: Exception
    op::Symbol
    R::Any
    findings::Vector{AbstractFinding}
end

function Base.showerror(io::IO, e::AbstractTypeError)
    print(io, "AbstractTypeError: ")
    _print_findings(io, e.op, e.R, e.findings)
    print(io, "\nFix the root causes, or relax `@error_on_abstract` to `@warn_on_abstract`.")
end

function _print_findings(io::IO, op, @nospecialize(R), fs::Vector{AbstractFinding})
    groups = Dict{String,Vector{AbstractFinding}}()
    order = String[]
    for f in fs
        root = isempty(f.origin) ? "(no origin found)" : last(f.origin)
        haskey(groups, root) || push!(order, root)
        push!(get!(groups, root, AbstractFinding[]), f)
    end
    # roots with uses in loops first
    sort!(order; by = r -> (-count(f -> f.inloop, groups[r]), -length(groups[r])))
    print(io, "`", op, "` at ", R, " uses abstract types on its normal path; ",
          length(order), length(order) == 1 ? " root cause:" : " root causes:")
    for (k, root) in enumerate(order)
        g = groups[root]
        nl = count(f -> f.inloop, g)
        f1 = something(findfirst(f -> f.inloop, g), 1)
        ex = g[f1]
        print(io, "\n  ", k, ". ", root,
              "\n       ", length(g), length(g) == 1 ? " use" : " uses", nl > 0 ? ", $nl in loops" : "",
              "; first", ex.inloop ? " in a loop" : "", ": ", ex.line, "  ", ex.use)
        for step in ex.origin[1:end-1]
            print(io, "\n       ← ", step)
        end
    end
end

# --- what counts as abstract ----------------------------------------------------

"Abstract for the purpose of concrete mode: not concrete, not a type constant, not a small union of concrete types."
function _isabstract(@nospecialize(T))
    T === Union{} && return false
    isconcretetype(T) && return false
    _CC.isType(T) && return false
    if T isa Union
        ts = Base.uniontypes(T)
        return !(length(ts) <= 4 && all(isconcretetype, ts))
    end
    return true
end

# builtins and functions whose use of an abstract value is free or narrows it
_benign(@nospecialize(f)) = f === Core.typeassert || f === Core.isa || f === Core.:(===) ||
    f === Core.typeof || f === Core.ifelse || f === Core.tuple || f === Core.isdefined ||
    f === Core.throw || f === Core.setfield! || f === Core.throw_methoderror || f === Core.:(!==)

# --- reading code -------------------------------------------------------------------

mutable struct _Tracer
    cx::_Walk
    owner::Any                                    # owner of the region's package
    srcs::IdDict{Core.MethodInstance,Any}         # typed code, or nothing
    rts::IdDict{Core.MethodInstance,Any}          # inferred return types
end

function _typed(tr::_Tracer, mi::Core.MethodInstance)
    get!(tr.srcs, mi) do
        m = mi.def
        m isa Method || return nothing
        res = try
            Base.code_typed_by_type(mi.specTypes; optimize = true, debuginfo = :source, world = tr.cx.world)
        catch
            nothing
        end
        res === nothing && return nothing
        for (ci, rt) in res
            if ci isa Core.CodeInfo && (ci.parent === nothing || ci.parent.def === m)
                tr.rts[mi] = rt
                return ci
            end
        end
        nothing
    end
end

_frames(src, mi, i) = try
    Base.IRShow.buildLineInfoNode(src.debuginfo, mi, i)
catch
    Any[]
end

function _frame_module(n)
    m = n.method
    m isa Core.MethodInstance && (m = m.def)
    return m isa Method ? m.module : nothing
end

"Inlined code of the trait machinery itself (operations, views, checked calls), which is not the module's code."
_machinery(frames) = any(n -> _frame_module(n) === TraitWorld, frames)

const _OWN_SRC = dirname(@__FILE__)

"A source file people wrote: package and script files carry absolute paths, Base's are relative."
_userfile(f) = (f = string(f); startswith(f, "/") && !startswith(f, _OWN_SRC) && !occursin("/share/julia/", f))

"The line a statement comes from, as people wrote it: the innermost frame in a user file."
function _userline(src, mi, i)
    fr = _frames(src, mi, i)
    for n in Iterators.reverse(fr)
        _userfile(n.file) && return string(basename(string(n.file)), ":", n.line)
    end
    for j in i-1:-1:1
        for n in Iterators.reverse(_frames(src, mi, j))
            _userfile(n.file) && return string(basename(string(n.file)), ":", n.line)
        end
    end
    l = _line(src, mi, i)
    return isempty(l) ? l : basename(l)
end

"Statements inside a loop body (between a back edge's target and its source)."
function _inloop(src)
    n = length(src.code)
    inl = falses(n)
    for i in 1:n
        st = src.code[i]
        tgt = st isa Core.GotoNode ? st.label : st isa Core.GotoIfNot ? st.dest : 0
        0 < tgt <= i && (inl[tgt:i] .= true)
    end
    return inl
end

_tstr(@nospecialize(T)) = string(T)
_callstr(f, ats) = string(f isa Function ? nameof(f) : f, "(", join(("::" * _tstr(T) for T in ats), ", "), ")")

function _mistr(mi::Core.MethodInstance)
    m = mi.def
    m isa Method || return string(mi)
    ps = mi.specTypes.parameters
    return string(m.module, ".", m.name, "(", join(("::" * _tstr(T) for T in ps[2:end]), ", "), ")")
end

# --- origins ----------------------------------------------------------------------

function _isboxnew(@nospecialize(st))
    Meta.isexpr(st, :new) && length(st.args) >= 1 || return false
    a = st.args[1]
    a isa GlobalRef && isdefined(a.mod, a.name) && (a = getglobal(a.mod, a.name))
    return a === Core.Box
end

"Where a boxed variable is first assigned: the first store into its box."
function _boxline(src, mi, @nospecialize(obj), fallback)
    b = _unpi(src, obj)
    b isa Core.SSAValue || return fallback
    for (j, st) in enumerate(src.code)
        if Meta.isexpr(st, :call) && length(st.args) >= 4 && st.args[3] == QuoteNode(:contents) &&
           _unpi(src, st.args[2]) === b
            f = st.args[1]
            f isa GlobalRef && isdefined(f.mod, f.name) && (f = getglobal(f.mod, f.name))
            f === Core.setfield! && return _userline(src, mi, j)
        end
    end
    return fallback
end

function _unpi(src, @nospecialize(x))
    while x isa Core.SSAValue && src.code[x.id] isa Core.PiNode
        x = src.code[x.id].val
    end
    return x
end

"Names of the variables a method boxes, in order of creation, from its lowered code."
function _lowered_boxes(m::Method)
    names = Symbol[]
    src = try Base.uncompressed_ir(m) catch; return names end
    for st in src.code
        if Meta.isexpr(st, :(=)) && st.args[1] isa Core.SlotNumber
            rhs = st.args[2]
            if Meta.isexpr(rhs, :call) && (rhs.args[1] === Core.Box || rhs.args[1] == GlobalRef(Core, :Box))
                push!(names, src.slotnames[st.args[1].id])
            end
        end
    end
    return names
end

"Name of the variable a `Core.Box` holds: the closure field it was read from, its creation order, or its undefined-variable check."
function _boxname(src, mi, @nospecialize(box))
    b = box
    while b isa Core.SSAValue && src.code[b.id] isa Core.PiNode
        b = src.code[b.id].val
    end
    if b isa Core.SSAValue
        d = src.code[b.id]
        if Meta.isexpr(d, :call) && length(d.args) >= 3 && d.args[3] isa QuoteNode   # getfield(closure, :name)
            return string(d.args[3].value)
        end
        if _isboxnew(d) && mi.def isa Method
            names = _lowered_boxes(mi.def)
            created = [j for j in eachindex(src.code) if _isboxnew(src.code[j])]
            k = findfirst(==(b.id), created)
            if k !== nothing && (length(names) == length(created) || length(names) == 1)
                return string(names[length(names) == 1 ? 1 : k])
            end
        end
    end
    for st in src.code
        if Meta.isexpr(st, :new) && length(st.args) >= 2
            T = st.args[1]
            T isa Type || continue
            for (k, a) in enumerate(st.args[2:end])
                a === b && T isa DataType && k <= fieldcount(T) && return string(fieldname(T, k))
            end
        end
    end
    for (j, st) in enumerate(src.code)
        if Meta.isexpr(st, :throw_undef_if_not) && st.args[1] isa Symbol
            c = st.args[2]
            if c isa Core.SSAValue
                d = src.code[c.id]
                if Meta.isexpr(d, :call) && length(d.args) >= 2
                    x = d.args[2]
                    while x isa Core.SSAValue && src.code[x.id] isa Core.PiNode
                        x = src.code[x.id].val
                    end
                    x === b && return string(st.args[1])
                end
            end
        end
    end
    return "?"
end

"The first returned value of abstract type in `src`."
function _abstract_return(src, sptypes)
    for st in src.code
        st isa Core.ReturnNode && isdefined(st, :val) || continue
        _isabstract(_argT(src, sptypes, st.val)) && return st.val
    end
    return nothing
end

function _trace!(out::Vector{String}, tr::_Tracer, src, sptypes, mi, @nospecialize(x), depth::Int, seen)::Bool
    if depth <= 0
        push!(out, "(trace stopped after 12 steps)")
        return true
    end
    T = _argT(src, sptypes, x)
    if x isa Core.Argument
        nm = x.n <= length(src.slotnames) ? src.slotnames[x.n] : Symbol("arg", x.n)
        push!(out, "argument `$(nm)` of $(_mistr(mi)) has type $(_tstr(T)), given by its caller")
        return true
    elseif x isa GlobalRef
        push!(out, isdefined(x.mod, x.name) && isconst(x.mod, x.name) ?
              "global `$(x.mod).$(x.name)` has type $(_tstr(T))" :
              "`$(x.mod).$(x.name)` is a non-constant global")
        return true
    elseif !(x isa Core.SSAValue)
        push!(out, "a value of type $(_tstr(T))")
        return true
    end
    key = (mi, x.id)
    key in seen && return false          # a cycle through a loop-carried variable
    push!(seen, key)
    d = src.code[x.id]
    ln = _userline(src, mi, x.id)
    # try each input in turn; keep the first trace that reaches a root
    function first_root(inputs)
        for a in inputs
            _isabstract(_argT(src, sptypes, a)) || continue
            n0 = length(out)
            _trace!(out, tr, src, sptypes, mi, a, depth - 1, seen) && return true
            resize!(out, n0)
        end
        return false
    end
    if d isa Core.PiNode
        return _trace!(out, tr, src, sptypes, mi, d.val, depth, seen)
    elseif d isa Core.PhiNode
        vals = Any[d.values[k] for k in eachindex(d.values) if isassigned(d.values, k)]
        first_root(vals) && return true              # the type was lost before the merge
        ts = unique!(Any[_argT(src, sptypes, v) for v in vals])
        any(_isabstract, ts) && return false
        push!(out, "a variable takes the types $(join(map(_tstr, ts), ", ")) on different paths ($ln)")
        return true
    elseif Meta.isexpr(d, :invoke)
        c = d.args[1]
        cmi = c isa Core.CodeInstance ? c.def : c
        isdefined(Core, :ABIOverride) && cmi isa Core.ABIOverride && (cmi = cmi.def)
        if !(cmi isa Core.MethodInstance)
            push!(out, "a call returns $(_tstr(T)) ($ln)")
            return true
        end
        push!(out, "$(_mistr(cmi)) returns $(_tstr(T)) ($ln)")
        csrc = _typed(tr, cmi)
        csrc === nothing && return true
        csp = _CC.sptypes_from_meth_instance(cmi)
        rv = _abstract_return(csrc, csp)
        rv === nothing && return true
        n0 = length(out)
        _trace!(out, tr, csrc, csp, cmi, rv, depth - 1, seen) || resize!(out, n0)
        return true
    elseif Meta.isexpr(d, :call)
        cl = _callee(src, sptypes, d.args[1])
        if cl[1] === :const && cl[2] === Core.getfield && length(d.args) >= 3
            obj = d.args[2]
            OT = _argT(src, sptypes, obj)
            fld = d.args[3] isa QuoteNode ? d.args[3].value : d.args[3]
            if OT === Core.Box
                at = _boxline(src, mi, obj, ln)
                push!(out, "variable `$(_boxname(src, mi, obj))` is boxed: a closure captures it and it is reassigned ($at)")
                return true
            elseif OT isa DataType && isconcretetype(OT) && (fld isa Symbol || fld isa Int)
                FT = try fieldtype(OT, fld) catch; Any end
                push!(out, "field `$(fld)` of `$(_tstr(OT))` is declared `$(_tstr(FT))` ($ln)")
                return true
            else
                push!(out, "field `$(fld)` is read from a value of type $(_tstr(OT)) ($ln)")
                first_root(Any[obj]) && return true
                return true
            end
        elseif cl[1] === :field
            push!(out, "the call through `$(cl[3])` of `$(_tstr(cl[2]))` returns $(_tstr(T)) ($ln)")
            return true
        elseif cl[1] === :const && cl[2] isa Core.Builtin && !any(a -> _isabstract(_argT(src, sptypes, a)), d.args[2:end])
            C = length(d.args) >= 2 ? _argT(src, sptypes, d.args[2]) : Any
            push!(out, "a container with an abstract element type: `$(nameof(cl[2]))` reads `$(_tstr(T))` from `$(_tstr(C))` ($ln)")
            return true
        elseif cl[1] === :const
            f = cl[2]
            ats = Any[_argT(src, sptypes, a) for a in d.args[2:end]]
            push!(out, "dynamic call $(_callstr(f, ats)) returns $(_tstr(T)) ($ln)")
            first_root(d.args[2:end])
            return true
        else
            push!(out, "a call through a value of type $(_tstr(cl[2])) ($ln)")
            first_root(Any[d.args[1]])
            return true
        end
    elseif Meta.isexpr(d, :foreigncall)
        push!(out, "a ccall returns $(_tstr(T)) ($ln)")
        return true
    elseif Meta.isexpr(d, :new)
        # a closure or struct whose type parameters follow abstract captured values
        push!(out, "`$(_tstr(T))` is built from values of abstract type ($ln)")
        first_root(d.args[2:end])
        return true
    else
        push!(out, "a value of type $(_tstr(T)) ($ln)")
        return true
    end
end

# --- the check ----------------------------------------------------------------------

"""
    concrete_findings(sig) -> Vector{AbstractFinding}

Every use of an abstract value on a normal path of the worker selected by the
call signature `sig`, and of the functions of its own package it calls, each
traced to its root cause.
"""
function concrete_findings(@nospecialize(sig))
    world = Base.get_world_counter()
    F = _worker_ftype(sig)
    tr = _Tracer(_Walk(world), owner(F.name.module), IdDict{Core.MethodInstance,Any}(), IdDict{Core.MethodInstance,Any}())
    root = _target_mi(sig, world)
    root === nothing && return AbstractFinding[]
    findings = AbstractFinding[]
    visited = Base.IdSet{Core.MethodInstance}()
    work = Core.MethodInstance[root]
    while !isempty(work)
        mi = pop!(work)
        mi in visited && continue
        push!(visited, mi)
        m = mi.def
        m isa Method && owner(m.module) === tr.owner || continue
        src = _typed(tr, mi)
        src === nothing && continue
        sptypes = _CC.sptypes_from_meth_instance(mi)
        succ = _succs(src)
        intry = _intry(src, succ)
        doomed = _doomed(src, succ, intry, c -> _throws_only(tr.cx, c))
        loops = _inloop(src)
        nf = length(findings)
        for i in eachindex(src.code)
            doomed[i] && continue
            st = src.code[i]
            fr = _frames(src, mi, i)
            _machinery(fr) && continue
            uses = Any[]
            usestr = ""
            if Meta.isexpr(st, :invoke)
                c = st.args[1]
                cmi = c isa Core.CodeInstance ? c.def : c
                isdefined(Core, :ABIOverride) && cmi isa Core.ABIOverride && (cmi = cmi.def)
                cmi isa Core.MethodInstance && push!(work, cmi)
                uses = st.args[3:end]
                usestr = cmi isa Core.MethodInstance ? _mistr(cmi) : "a call"
            elseif Meta.isexpr(st, :call)
                cl = _callee(src, sptypes, st.args[1])
                cl[1] === :const && _benign(cl[2]) && continue
                ats = Any[_argT(src, sptypes, a) for a in st.args[2:end]]
                if cl[1] === :field
                    # a witness call through the erased table: its callee is abstract by design
                    uses = st.args[2:end]
                    usestr = _callstr(cl[3], ats)
                elseif cl[1] === :const
                    uses = st.args[2:end]
                    usestr = _callstr(cl[2], ats)
                else
                    uses = st.args[1:end]
                    usestr = "a call through a value of type $(_tstr(cl[2]))"
                end
            elseif st isa Core.ReturnNode && isdefined(st, :val)
                uses = Any[st.val]
                usestr = "returns ::" * _tstr(_argT(src, sptypes, st.val))
            else
                continue
            end
            for a in uses
                _isabstract(_argT(src, sptypes, a)) || continue
                origin = String[]
                _trace!(origin, tr, src, sptypes, mi, a, 12, Set{Any}())
                push!(findings, AbstractFinding(_userline(src, mi, i), usestr, loops[i], origin))
                break      # one finding per statement
            end
        end
        # the result type callers see: inference can widen it before the optimizer removes
        # the cause (a boxed variable, typically), leaving concrete code with an abstract result
        rt = get(tr.rts, mi, nothing)
        if rt !== nothing && _isabstract(_CC.widenconst(rt)) && !any(f -> startswith(f.use, "returns"), findings[nf+1:end])
            boxes = _lowered_boxes(m)
            origin = isempty(boxes) ? String["inference widened the result to $(_tstr(rt)) before optimization"] :
                     String["variable `$(join(boxes, "`, `"))` is boxed in the lowered code: a closure captures it and it is reassigned"]
            pushfirst!(origin, "$(_mistr(mi)) is inferred to return $(_tstr(rt))")
            push!(findings, AbstractFinding(isa(m, Method) ? string(basename(string(m.file)), ":", m.line) : "",
                                            "result type ::" * _tstr(rt), false, origin))
        end
    end
    return findings
end

"""
    concrete_level(f) -> :off, :warn or :error

Concrete mode of a trait module's function: set per function with
`@warn_on_abstract` or `@error_on_abstract` inside the module, or for the
whole module by putting the macro in front of `@trait_module`.
"""
concrete_level(@nospecialize(f)) = _module_concrete(parentmodule(f))
function _module_concrete(m::Module)
    while true
        isdefined(m, :__tw_concrete__) && return getfield(m, :__tw_concrete__)::Symbol
        p = parentmodule(m)
        p === m && return :off
        m = p
    end
end

"Describe the representations of a worker signature, for messages."
_sig_reps(@nospecialize(sig)) = join([string(nameof(v.parameters[1]), " at ", v.parameters[3])
                                      for T in sig.parameters if _istobj(T) for v in T.parameters[2].parameters], ", ")

"Run concrete mode for a worker signature, per its function's level: warn once, or throw."
function _check_concrete(@nospecialize(sig))
    F = _worker_ftype(sig)
    f = F.instance
    lv = Base.invokelatest(concrete_level, f)::Symbol
    lv === :off && return nothing
    fs = concrete_findings(sig)
    d = get(WORKER_DOORS, sig, nothing)
    if d !== nothing && (!isempty(d.outward) || d.truncated)
        # outward doors are dynamic calls upward; the budget's end is reported, never admitted by silence
        msg = "`$(nameof(f))` at $(_sig_reps(sig)): " * (isempty(d.outward) ? "" : "outward doors, dynamic calls upward: " * join(d.outward, "; ")) *
              (d.truncated ? (isempty(d.outward) ? "" : "; ") * "the walk into Base stopped at its budget ($(DOOR_BUDGET[]) method instances): unchecked beyond it" : "")
        @warn "@warn_on_abstract: " * msg
    end
    isempty(fs) && return nothing
    lv === :error && throw(AbstractTypeError(nameof(f), _sig_reps(sig), fs))
    @warn "@warn_on_abstract: " * sprint(_print_findings, nameof(f), _sig_reps(sig), fs)
    return nothing
end

"""
    check_concrete(f, sig_or_args...) -> Vector{AbstractFinding}

Concrete mode's findings for a worker signature, whatever the function's
level: for tests and CI.
"""
check_concrete(@nospecialize(sig::Type)) = concrete_findings(sig)

const _CONCRETE_MACROS = (Symbol("@warn_on_abstract"), Symbol("@error_on_abstract"))
function _concrete_macro_level(@nospecialize(head))
    s = head isa GlobalRef ? head.name : head isa Expr && head.head === :. ? head.args[end].value : head
    return s === Symbol("@warn_on_abstract") ? :warn : s === Symbol("@error_on_abstract") ? :error : nothing
end

function _annotate_module(ex, level::Symbol, which::String)
    if ex isa Expr && ex.head === :macrocall && endswith(string(ex.args[1]), "trait_module")
        body = ex.args[end]
        stmt = :(const __tw_concrete__ = $(QuoteNode(level)))
        if body isa Expr && body.head === :module
            newbody = Expr(:block, stmt, body.args[3].args...)
            return Expr(:macrocall, ex.args[1:end-1]..., Expr(:module, body.args[1], body.args[2], newbody))
        elseif body isa Expr && body.head === :block
            return Expr(:macrocall, ex.args[1:end-1]..., Expr(:block, stmt, body.args...))
        end
    end
    error("$which applies to a `@trait_module`, or to a function inside one")
end

"""
    @warn_on_abstract @trait_module begin … end
    @warn_on_abstract f(t::ColTable, …) = …          # inside a trait module

Concrete mode with warnings: the first time a function runs at a
representation (or a package image compiles it there), warn if its code uses
abstract types on a normal path, naming each root cause.
"""
macro warn_on_abstract(ex)
    esc(_annotate_module(ex, :warn, "@warn_on_abstract"))
end

"""
    @error_on_abstract @trait_module begin … end
    @error_on_abstract f(t::ColTable, …) = …         # inside a trait module

Concrete mode with errors: the function raises `AbstractTypeError` instead of
running when its code uses abstract types on a normal path.
"""
macro error_on_abstract(ex)
    esc(_annotate_module(ex, :error, "@error_on_abstract"))
end
