# ---------------------------------------------------------------------------
# Diagnostics for slowdowns (W-85):
#   - `callpath(f, args...)`: the path a call into trait code takes, per bounded argument, and its cost;
#   - `factscode(f, types)`: the code compiled by facts for a signature, its run-time sites marked;
#   - `loadreport()`: what the machinery's checks and folds cost during loads and first uses (report.jl).
# They read the machinery's state and Julia's reflection; they change nothing a call would not change.
# ---------------------------------------------------------------------------

public callpath, factscode, loadreport, loadreport_switch!, descend_facts, facts_provider

# --- printing helpers -------------------------------------------------------------------

"A type or value as one short line: TraitWorld's type printers, cut at `n` characters."
function _dshort(@nospecialize(x), n::Int = 140)
    s = sprint(show, x; context = :compact => true)
    s = replace(s, r"\s+" => " ")
    return length(s) <= n ? s : first(s, n - 1) * "…"
end
_ms(ns) = string(round(ns / 1e6; digits = 1))

# --- run-time sites in optimized code ------------------------------------------------------

"""
A run-time site of compiled code: a call whose target is chosen when it runs. `kind` is `:dispatch` (a
dynamic dispatch), `:split_table` (a call-site split's last branch: a lookup by the value's type, then a
call through a pointer), `:pointer` (a call through a pointer: an untyped call's table, a `Dynamic`
function), `:apply` (a call through `Core._apply_iterate` and its kin), `:latest` (`invokelatest`, a call
in another world).
"""
struct RuntimeSite
    where_::String
    stmt::Int
    kind::Symbol
    call::String
    fname::String     # the called function as `call` names it (a dispatch), or ""
    loc::String
    note::String      # a path that does not run per call (an error, a first call, a first sight), or ""
end
RuntimeSite(w, i, k, c, l) = RuntimeSite(w, i, k, c, "", l, _site_note(c))
RuntimeSite(w, i, k, c, f, l) = RuntimeSite(w, i, k, c, f, l, _site_note(c))

"The machinery's paths that do not run per call, by the function a site calls."
const _RARE_PATHS = [
    "_check_once" => "the first-call check: once per signature",
    "_umiss" => "first sight of a type at a table", "_pmiss" => "first sight of a type at a table",
    "_conf_family_slow" => "a family member's first use",
    "_held_refused" => "an error path", "_rule3_error" => "an error path", "_cast_refuse" => "an error path",
    "_dyn_refuse" => "an error path", "_no_worker_error" => "an error path", "_closed_miss" => "an error path",
    "_dyn_nonconforming" => "an error path", "_like_return" => "only for a result like the input",
    "_like_out" => "only for a result like the input", "fallback(" => "the untyped fallback: a value without the traits",
    "kwfallback(" => "the untyped fallback: a value without the traits",
    "_register_candidate_slow!" => "first sight of a dynamic value's type",
]
function _site_note(call::AbstractString)
    for (k, v) in _RARE_PATHS
        occursin(k, call) && return v
    end
    return ""
end

"The type (or the constant) of an argument of statement code in `src`."
function _ir_type(@nospecialize(x), src::Core.CodeInfo)
    if x isa Core.SSAValue
        t = src.ssavaluetypes isa Vector{Any} ? src.ssavaluetypes[x.id] : Any
        return t
    elseif x isa Core.Argument
        st = src.slottypes
        return st isa Vector{Any} && x.n <= length(st) ? st[x.n] : Any
    elseif x isa GlobalRef
        return isdefined(x.mod, x.name) && isconst(x.mod, x.name) ? Core.Const(getglobal(x.mod, x.name)) : Any
    elseif x isa QuoteNode
        return Core.Const(x.value)
    elseif x isa Expr
        return Any
    end
    return Core.Const(x)
end
_ir_const(@nospecialize(t)) = t isa Core.Const ? (true, t.val) : (t isa Type && Base.issingletontype(t)) ? (true, t.instance) : (false, nothing)
_ir_widen(@nospecialize(t)) = t isa Core.Const ? Core.Typeof(t.val) : t isa Type ? t : CC.widenconst(t)

"Where statement `i` of `src` comes from: `file:line` of the innermost frame, and the method it is in."
function _ir_loc(src::Core.CodeInfo, i::Int)
    try
        lins = Base.IRShow.buildLineInfoNode(src.debuginfo, src.parent, i)
        j = i                                  # a statement the optimizer inserted (a split's table) has none: the one before it
        while isempty(lins) && j > max(1, i - 10)
            j -= 1
            lins = Base.IRShow.buildLineInfoNode(src.debuginfo, src.parent, j)
        end
        isempty(lins) && return ""
        fr = String[]
        for l in lins
            m = l.method
            mn = m isa Core.MethodInstance ? string(m.def isa Method ? m.def.name : m.def) : m isa Method ? string(m.name) : string(m)
            push!(fr, string(mn, " ", basename(string(l.file)), ":", l.line))
        end
        length(fr) > 3 && (fr = vcat(fr[1:1], ["…"], fr[end-1:end]))
        return join(fr, " → ")
    catch
        return ""
    end
end

"A split's called function, as an operation on a dynamic value where it is one, and the candidates of its trait now."
function _split_callee(@nospecialize(F))
    if F isa DataType && F.name.name === :_DynOp && length(F.parameters) == 2
        X, opT = F.parameters
        op = isdefined(opT, :instance) ? opT.instance : opT
        return string(_dshort(op, 40), " on a Dynamic{", _dshort(X, 50), "}"), CC.dynamic_candidates(_family_of(X))
    end
    return (isdefined(F, :instance) ? _dshort(F.instance, 50) : _dshort(F, 50)), nothing
end

"The name a `foreigncall` calls (a symbol), or the expression of its pointer."
_fc_name(@nospecialize(name)) = name isa QuoteNode ? name.value : (name isa Expr && name.head === :tuple && !isempty(name.args)) ?
    (name.args[1] isa QuoteNode ? name.args[1].value : name.args[1]) : name

const _APPLY_BUILTINS = Any[Core._apply_iterate, Core._apply, Core._call_latest, Core._call_in_world, Core.invoke_in_world]

"The run-time sites of statement code `src`, and the code instances it invokes."
function _ir_sites(src::Core.CodeInfo, where_::String)
    sites = RuntimeSite[]
    invoked = Any[]
    for (i, stmt) in enumerate(src.code)
        stmt isa Expr || continue
        if stmt.head === :call
            ft = _ir_type(stmt.args[1], src)
            isc, f = _ir_const(ft)
            barrier = false
            if !isc && stmt.args[1] isa Core.SSAValue      # a callee behind an inference barrier: named by its value
                d = src.code[stmt.args[1].id]
                if d isa Expr && d.head === :call && length(d.args) == 3 && _ir_const(_ir_type(d.args[1], src)) == (true, Core.compilerbarrier)
                    isc, f = _ir_const(_ir_type(d.args[3], src))
                    barrier = isc
                end
            end
            if isc && (f isa Core.IntrinsicFunction || (f isa Core.Builtin && !any(b -> b === f, _APPLY_BUILTINS)))
                f === Core.invoke || continue      # a static invoke with a known method is not a run-time site
            end
            kind = isc && f isa Core.Builtin ? (f === Core._call_latest || f === Core._call_in_world || f === Core.invoke_in_world ? :latest : :apply) : :dispatch
            argts = Any[_ir_widen(_ir_type(a, src)) for a in stmt.args[2:end]]
            fname = isc ? _dshort(f, 60) : "(" * _dshort(_ir_widen(ft), 60) * ")"
            barrier && (fname = "inferencebarrier(" * fname * ")")
            call = string(fname, "(", join((string("::", _dshort(t, 70)) for t in argts), ", "), ")")
            push!(sites, RuntimeSite(where_, i, kind, call, fname, _ir_loc(src, i)))
        elseif stmt.head === :foreigncall
            name = stmt.args[1]
            nm = _fc_name(name)
            if nm === :jl_split_table_ptr
                tbl = length(stmt.args) >= 6 ? stmt.args[6] : nothing
                tbl isa QuoteNode && (tbl = tbl.value)
                what = try
                    F = getfield(tbl, :f); A = getfield(tbl, :args)
                    fn, cands = _split_callee(F)
                    string(fn, "(::<a type outside the candidates>", join((string(", ::", _dshort(t, 50)) for t in A.parameters)), ")",
                           cands === nothing ? "" : string("; the candidates now: ", isempty(cands) ? "none" : join((_dshort(c, 40) for c in cands), ", ")))
                catch
                    "a call"
                end
                push!(sites, RuntimeSite(where_, i, :split_table, what, _ir_loc(src, i)))
            elseif nm isa Core.SSAValue && (d = src.code[nm.id]; d isa Expr && d.head === :foreigncall && _fc_name(d.args[1]) === :jl_split_table_ptr)
                continue                         # the split table's call through its pointer: counted with its lookup
            elseif !(nm isa Symbol || nm isa String)
                push!(sites, RuntimeSite(where_, i, :pointer, string("a call through a pointer returning ", _dshort(stmt.args[2], 40)), _ir_loc(src, i)))
            end
        elseif stmt.head === :invoke
            push!(invoked, stmt.args[1])
        end
    end
    return sites, invoked
end

# --- factscode ------------------------------------------------------------------------------

"Why a body's code does not run per call (the untyped fallback, an error's construction), or `nothing`."
function _rare_body(mi::Core.MethodInstance)
    m = mi.def
    m isa Method || return nothing
    m.module === TraitWorld && m.name in (:fallback, :kwfallback) && return "the untyped fallback: a value without the traits"
    startswith(string(m.name), "throw") && return "an error path"
    T = mi.specTypes.parameters[1]
    T isa DataType && T <: Type && T.parameters[1] isa DataType && T.parameters[1] <: Exception && return "an error path"
    return nothing
end

"A body of code that `factscode` read: its method instance, its optimized code, its result type, its owner."
struct CodeBody
    mi::Core.MethodInstance
    src::Core.CodeInfo
    rt::Any
    owner::Any
end
"What `factscode` found: the bodies it read from the signature down, and their run-time sites."
struct FactsCode
    sig::Any
    bodies::Vector{CodeBody}
    sites::Vector{RuntimeSite}
    ir::Bool
end

_mi_where(mi::Core.MethodInstance) = _dshort(mi.specTypes, 160)

"""
    factscode(f, types; depth = 2, plain = false, ir = false)
    factscode(sig::Type{<:Tuple}; …)

The code inference compiles by facts for the call `f(::types...)`, optimized, and its run-time sites:
calls whose target is chosen when they run (a dynamic dispatch, a call-site split's table, a call through
a pointer, `invokelatest`). The code it invokes statically is read as well, `depth` levels down, where it
is code of the facts owner (`plain = true`: any code). With `ir = true` the code itself is printed, each
run-time site marked in its listing.

Plain inference (`plain = true` and the caller of a trait module) is read with Julia's native interpreter;
`Cthulhu`'s interactive descent over the facts owner's code is not available here.
"""
factscode(@nospecialize(f), @nospecialize(types); kw...) = factscode(Base.signature_type(f, types); kw...)

function factscode(@nospecialize(sig::Type); depth::Int = 2, plain::Bool = false, ir::Bool = false, facts::Bool = true)
    nat = CC.NativeInterpreter(Base.get_world_counter())
    interp = facts ? CC.facts_interp(nat) : nat
    bodies = CodeBody[]
    sites = RuntimeSite[]
    seen = Base.IdSet{Any}()
    function visit(@nospecialize(s), d::Int)
        s in seen && return
        push!(seen, s)
        res = try
            Base.code_typed_by_type(s; optimize = true, interp, debuginfo = :source)
        catch e
            push!(sites, RuntimeSite(_dshort(s, 160), 0, :error, sprint(showerror, e)[1:min(end, 200)], ""))
            return
        end
        for (src, rt) in res
            src isa Core.CodeInfo || continue
            mi = src.parent
            mi isa Core.MethodInstance || (mi = Base.method_instances(s)[1])
            push!(bodies, CodeBody(mi, src, rt, interp isa CC.NativeInterpreter ? CC.cache_owner(interp) : nothing))
            ss, inv = _ir_sites(src, _mi_where(mi))
            rare = _rare_body(mi)
            rare === nothing || (ss = RuntimeSite[RuntimeSite(x.where_, x.stmt, x.kind, x.call, x.fname, x.loc, rare) for x in ss])
            append!(sites, ss)
            d > 0 || continue
            for c in inv
                c isa Core.CodeInstance || continue
                (plain || c.owner === FACTS_OWNER) || continue
                cm = c.def isa Core.MethodInstance ? c.def : c.def.def
                cm isa Core.MethodInstance && cm.def isa Method || continue
                visit(cm.specTypes, d - 1)
            end
        end
    end
    visit(sig, depth)
    return FactsCode(sig, bodies, sites, ir)
end

const _SITE_TEXT = Dict(:dispatch => "dynamic dispatch", :split_table => "a split's last branch: a table by the value's type, a call through its pointer",
                        :pointer => "call through a pointer", :apply => "apply (arguments as a collection)",
                        :latest => "call in another world (invokelatest)", :error => "not inferred")

function Base.show(io::IO, ::MIME"text/plain", fc::FactsCode)
    owner = isempty(fc.bodies) ? "?" : string(something(fc.bodies[1].owner, "plain"))
    println(io, "factscode: ", _dshort(fc.sig, 200))
    println(io, "  code of the owner ", owner, "; ", length(fc.bodies), " bodies read (the signature, then what it invokes statically)")
    for b in fc.bodies
        n = count(s -> s.where_ == _mi_where(b.mi), fc.sites)
        println(io, "    ", _dshort(b.mi.specTypes, 150), " → ", _dshort(b.rt, 60), "; ", length(b.src.code), " statements, ",
                n, " run-time site", n == 1 ? "" : "s")
    end
    _show_sites(io, fc.sites, "  ", true)
    if fc.ir
        for b in fc.bodies
            println(io)
            println(io, "  ── ", _dshort(b.mi.specTypes, 200))
            marks = Dict(s.stmt => s.kind for s in fc.sites if s.where_ == _mi_where(b.mi))
            lines = split(sprint(show, b.src; context = io), '\n')
            for l in lines
                m = match(r"^\s*(\d+)\s", l)
                m2 = match(r"%(\d+)\s*=", l)
                k = m2 !== nothing ? get(marks, parse(Int, m2.captures[1]), nothing) : nothing
                println(io, k === nothing ? "    " : "  ▶ ", l, k === nothing ? "" : "    # run-time site: " * _SITE_TEXT[k])
            end
        end
    end
end
"Print run-time sites: those on every call's path first, then the rare paths (an error, a first call)."
function _show_sites(io::IO, sites::Vector{RuntimeSite}, ind::String, where_::Bool)
    hot = filter(s -> isempty(s.note), sites); rare = filter(s -> !isempty(s.note), sites)
    println(io, ind, "run-time sites: ", isempty(hot) ? "none" : length(hot), isempty(rare) ? "" : string(" (and ", length(rare), " on rare paths)"))
    for s in hot
        println(io, ind, "  [", _SITE_TEXT[s.kind], "] ", s.call)
        (where_ || !isempty(s.loc)) && println(io, ind, "      ", where_ ? string("in ", s.where_, " %", s.stmt, isempty(s.loc) ? "" : ", ") : "", s.loc)
    end
    for s in rare
        println(io, ind, "  rare: ", s.note, ": ", s.call)
    end
end
Base.show(io::IO, fc::FactsCode) = print(io, "FactsCode(", _dshort(fc.sig, 80), "; ", length(fc.sites), " run-time sites)")

# --- callpath -------------------------------------------------------------------------------

"A typed caller: the entry is inlined into it, at the arguments' types."
@inline _cp_typed(f::F, args::Vararg{Any,N}) where {F,N} = f(args...)
"`n` calls from a typed caller."
@noinline function _cp_loop_typed(f::F, args::A, n::Int) where {F,A<:Tuple}
    for _ in 1:n
        Base.donotdelete(f(args...))
    end
    return nothing
end
"`n` calls from a caller that does not know the arguments' types: a dispatch per call, at a fixed arity."
@generated function _cp_loop_untyped(f::F, xs::Vector{Any}, ::Val{N}, n::Int) where {F,N}
    call = Expr(:call, :f, [:(xs[$i]) for i in 1:N]...)
    return quote
        for _ in 1:n
            Base.donotdelete($call)
        end
        return nothing
    end
end
"The time (ns) and bytes per call of `run(n)`: warmed up, `n` chosen for about 20 ms, the minimum of three."
function _cp_time(run)
    run(1); run(1)
    t1 = @elapsed run(100)
    n = clamp(round(Int, 0.02 / max(t1 / 100, 1e-9)), 100, 10^7)
    t = minimum(@elapsed(run(n)) for _ in 1:3)
    b = @allocated run(n)
    return t * 1e9 / n, b / n
end

"How the value at a bounded position arrives: its form and the object it stands for."
function _cp_form(@nospecialize(a))
    a isa TObj && return "a trait object (refused at an entry: rule 3)", a
    a isa CompiledFor && return "compiled_for(::$(_dshort(typeof(getfield(a, :x)), 60)))", getfield(a, :x)
    a isa WithDynamic && return "with_dynamic(::$(_dshort(typeof(getfield(a, :x)), 60)))", getfield(a, :x)
    if a isa HeldValue
        o = getfield(a, :t)
        att = a isa Kept ? (getfield(a, :compiled) ? ", its attribute Compiled" : ", its attribute Dynamic") : ""
        return string(_dshort(typeof(a), 60), att, " holding ", o isa TObj ? "a trait object" : _dshort(typeof(o), 60)), o
    end
    return string("plain ", _dshort(typeof(a), 80)), a
end

"How trait `X`'s implementation for `U` is found: declared, a family's (and its member's state), generic, or none."
function _cp_impl(@nospecialize(X), @nospecialize(o))
    U = typeof(o)
    U isa DataType || return "not a concrete type"
    mn, mx = Ref{UInt}(typemin(UInt)), Ref{UInt}(typemax(UInt))
    m = ccall(:jl_gf_invoke_lookup_worlds, Any, (Any, Any, UInt, Ptr{Csize_t}, Ptr{Csize_t}),
              Tuple{typeof(conformance),As{X},U}, nothing, Base.get_world_counter(), mn, mx)
    m isa Core.MethodMatch || return "none"
    meth = m.method
    if meth.sig isa DataType && meth.sig.parameters[3] === U
        return "declared for $(_dshort(U, 60)) ($(meth.module))"
    end
    if meth.module !== TraitWorld
        reg = _cp_family_registry(meth)
        st = reg === nothing ? "its registry not found" :
             get(reg[], U, nothing) isa Builder ? "fixed in this session" :
             Pair{Any,Any}(X, U) in (@atomic _FOLD_FINAL.s) ? "never folded (its builder holds a session's pointers, or it failed)" :
             "not fixed yet (fixed at its first use, or where a caller is compiled)"
        return "a family's member ($(meth.module), $(meth.file):$(meth.line)): $st"
    end
    v = try Base.invokelatest(conformance, As{X}(), o) catch; nothing end    # as the call asks (the slow path, cached)
    v === NOTRAIT && return "none: no method of its own, so each call that needs it asks the slow path's cache (`_conformance_slow`, an IdDict by trait and type)"
    return "generic or dynamic: no method of its own, so each call that needs it asks the slow path's cache (`_conformance_slow`)"
end
"The builder registry of a family implementation's `conformance` method (a constant its body reads)."
function _cp_family_registry(meth::Method)
    try
        src = Base.uncompressed_ast(meth)
        for st in src.code
            for x in (st isa Expr ? st.args : Any[st])
                x isa GlobalRef && occursin("family_builders", string(x.name)) && isdefined(x.mod, x.name) &&
                    return getglobal(x.mod, x.name)
                if x isa Expr
                    for y in x.args
                        y isa GlobalRef && occursin("family_builders", string(y.name)) && isdefined(y.mod, y.name) &&
                            return getglobal(y.mod, y.name)
                    end
                end
            end
        end
    catch
    end
    return nothing
end

"One bounded position's path: what arrives, what the position needs, what the entry decides for each caller."
struct PositionPath
    pos::Int
    form::String
    object::Any
    needs::Vector{Any}
    attribute::Any
    impls::Vector{String}
    typed::String
    untyped::String
    tobj_typed::Any
    decided_at_run_time::Bool
end
"What `callpath` found."
struct CallPath
    call::String
    entry::Any
    tabled::Bool
    positions::Vector{PositionPath}
    worker::Any
    worker_sig::Any
    caller_sites::Vector{RuntimeSite}
    folded::Vector{String}
    worker_sites::Vector{RuntimeSite}
    typed_ns::Float64
    typed_bytes::Float64
    untyped_ns::Float64
    untyped_bytes::Float64
end

"The worker's code of a call `callpath` read: `factscode(callpath(f, x))`."
factscode(c::CallPath; kw...) = c.worker_sig === nothing ? error("callpath found no worker for $(c.call)") : factscode(c.worker_sig; kw...)

"The entry's decision for a value at position `p`, from a caller that knows its type (`kn`) or not."
function _cp_decide(p::EntryPos, @nospecialize(a), kn::Bool, tabled::Bool)
    known = _known_object(a, kn)
    if tabled && !known && _tabled(p, a)
        u = _unconverted(a)
        e = _ulookup(_utable(p), XAny(u), Base.get_world_counter())
        st = e === nothing ? "not in the table yet (added at the first call)" : e isa Builder ? "in the table" :
             e === _UNTABLED ? "in the table as not served: the entry's own path" : "in the table as conforming to none"
        return string("Compiled, through the table of declared implementations: the builder for ", _dshort(typeof(u), 60),
                      " looked up by type, then the entry's method for its key through a pointer (_UWrap: arguments boxed); ", st), nothing
    end
    v = try
        enter(p, a, Val(kn))
    catch e
        return string("refused: ", sprint(showerror, e)[1:min(end, 200)]), nothing
    end
    v === NOTRAIT && return "no trait the position needs: the untyped fallback", nothing
    V = typeof(v).parameters[2]
    how = _is_erased(V) ? "Dynamic: the erased key (code compiled once)" : "Compiled at its key"
    why = a isa HeldValue ? " (the held value's attribute)" : a isa CompiledFor ? " (compiled_for)" : a isa WithDynamic ? " (with_dynamic)" :
          (attribute(p) !== nothing ? " (the position's attribute)" : _traits_default(needed(p)) !== nothing ? " (the traits' default)" :
           kn ? " (the caller knows the type)" : " (the caller does not know the type)")
    return string(how, why, ": ", _dshort(typeof(v), 120)), v
end

"""
    callpath(f, args...; time = true)

The path a call `f(args...)` into trait code takes, for a caller that knows the arguments' types (typed)
and for one that does not (untyped): per bounded argument, the form of the value (plain, `Compiled`,
`Dynamic`, `Kept`, a cast), the traits the position needs and how each is implemented for the object's
type (declared, a family's member fixed or not, generic), and what the entry decides (the trait object at
its key, the erased key, the table of declared implementations through a pointer); the worker the call
reaches; the run-time sites left in the typed caller's code and in the worker's (see `factscode`); and the
call's time and allocation per call from both callers. The call is made (to time it): its first-call
checks and table entries happen as they would.
"""
function callpath(@nospecialize(f), args...; time::Bool = true)
    nargs = length(args)
    types = Any[typeof(a) for a in args]
    call = string(_dshort(f, 60), "(", join((string("::", _dshort(T, 60)) for T in types), ", "), ")")
    entry = try which(f, Tuple{types...}) catch; nothing end
    mod = entry isa Method ? entry.module : parentmodule(f)
    poss = Int[]
    if isdefined(mod, :__tw_positions__)
        for (g, pos, n) in mod.__tw_positions__
            g === f && (n == nargs || n == -1) && pos <= nargs && !(pos in poss) && push!(poss, pos)
        end
    end
    sort!(poss)
    tabled = isdefined(mod, :__tw_untyped__) && any(x -> x[1] === f && x[2] == nargs, mod.__tw_untyped__)
    paths = PositionPath[]
    views = Any[args...]
    for pos in poss
        p = EntryPos{typeof(f),pos,nargs}()
        a = args[pos]
        form, o = _cp_form(a)
        L = needed(p)
        Xs = Any[(L isa TraitList ? typeof(L) : L).parameters[1].parameters...]
        impls = String[string(_dshort(X, 60), ": ", _cp_impl(X, o)) for X in Xs]
        ty, v = _cp_decide(p, a, true, tabled)
        un, _ = _cp_decide(p, a, false, tabled)
        v === nothing || (views[pos] = v)
        # whether the caller's compiler knows the trait object's type, or it is decided when the call runs
        rt = try
            Base.return_types(enter, (typeof(p), typeof(a), Val{true}))
        catch
            Any[]
        end
        runtime = length(rt) == 1 && !(isconcretetype(rt[1]) || rt[1] === NoTrait) && !(a isa Compiled || (a isa Kept && getfield(a, :compiled)))
        push!(paths, PositionPath(pos, form, typeof(o), Xs, attribute(p), impls, ty, un, v === nothing ? nothing : typeof(v), runtime))
    end
    worker = isempty(poss) ? nothing : try which(f, Tuple{Any[typeof(v) for v in views]...}) catch; nothing end
    # the typed caller's compiled code: the entry inlined at the arguments' types
    csites = RuntimeSite[]
    folded = String[]
    try
        for (src, _) in Base.code_typed(_cp_typed, Tuple{typeof(f),types...}; optimize = true, debuginfo = :source)
            ss, _ = _ir_sites(src, "the typed caller")
            append!(csites, ss)
            for st in src.code
                st isa Expr && st.head in (:call, :invoke) || continue
                s = string(st)
                for nm in ("_conf_family", "_conformance_slow", "_member_fix!", "_umiss", "_pmiss")
                    occursin(nm, s) && !(nm in folded) && push!(folded, nm)
                end
            end
        end
    catch
    end
    wsites = RuntimeSite[]
    if worker isa Method
        try
            wsites = factscode(Tuple{typeof(f),Any[typeof(v) for v in views]...}; depth = 1).sites
        catch
        end
    end
    tn = tb = un = ub = NaN
    if time
        tn, tb = _cp_time(n -> _cp_loop_typed(f, args, n))
        xs = Any[args...]
        un, ub = _cp_time(n -> _cp_loop_untyped(f, xs, Val(nargs), n))
    end
    wsig = worker isa Method ? Tuple{typeof(f),Any[typeof(v) for v in views]...} : nothing
    return CallPath(call, entry, tabled, paths, worker, wsig, csites, folded, wsites, tn, tb, un, ub)
end

function Base.show(io::IO, ::MIME"text/plain", c::CallPath)
    println(io, "callpath: ", c.call)
    if !(c.entry isa Method)
        println(io, "  no method")
    elseif isempty(c.positions)
        println(io, "  a plain method, not a bounded function's entry: ", c.entry)
    else
        println(io, "  entry: ", c.entry.module, ".", c.entry.name, ", bounded argument", length(c.positions) == 1 ? " " : "s ",
                join((string(p.pos) for p in c.positions), ", "),
                c.tabled ? "; untyped callers served by the table of declared implementations" : "; no table (untyped callers take the entry's path)")
    end
    for p in c.positions
        println(io, "  argument ", p.pos, ": ", p.form)
        println(io, "    the position needs ", join((_dshort(X, 60) for X in p.needs), ", "),
                p.attribute === nothing ? "" : string("; its attribute ", p.attribute))
        for s in p.impls
            println(io, "      ", s)
        end
        println(io, "    typed caller:   ", p.typed)
        println(io, "    untyped caller: ", p.untyped)
        p.decided_at_run_time &&
            println(io, "    the trait object's type is not known where the call is compiled: it is made when the call runs, ",
                    "and the worker is chosen by a dispatch on it (the object's traits)")
    end
    c.worker === nothing || println(io, "  worker: ", _worker_text(c.worker))
    if !isempty(c.positions)
        println(io, "  typed caller's code (the entry inlined):")
        _show_sites(io, c.caller_sites, "    ", false)
        isempty(c.folded) ||
            println(io, "    not folded there, run in the call: ", join(c.folded, ", "),
                    " (an implementation looked up when the call runs: a family member not fixed while the caller was compiled, or the slow path)")
        if c.worker !== nothing
            println(io, "  worker's code (compiled by facts, and what it invokes statically):")
            _show_sites(io, c.worker_sites, "    ", true)
        end
    end
    if !isnan(c.typed_ns)
        println(io, "  per call: typed caller ", round(c.typed_ns; sigdigits = 3), " ns, ", round(c.typed_bytes; digits = 1),
                " bytes; untyped caller ", round(c.untyped_ns; sigdigits = 3), " ns, ", round(c.untyped_bytes; digits = 1), " bytes")
    end
end
"A worker method as its bounds: `cb(::(IntegratorView, HasDu)) at x6.jl:30`."
function _worker_text(m::Method)
    sig = Base.unwrap_unionall(m.sig)
    ps = sig isa DataType ? sig.parameters[2:end] : Any[]
    args = String[]
    for p in ps
        lb = try _tobj_lb(p) catch; nothing end
        if lb === nothing
            push!(args, string("::", _dshort(p, 50)))
        else
            ts = Base.uniontypes(lb)
            push!(args, string("::", length(ts) == 1 ? _dshort(ts[1], 60) : "(" * join((_dshort(t, 40) for t in ts), ", ") * ")"))
        end
    end
    return string(m.name, "(", join(args, ", "), ") at ", basename(string(m.file)), ":", m.line, " (", m.module, ")")
end
_worker_text(@nospecialize(x)) = string(x)
Base.show(io::IO, c::CallPath) = print(io, "CallPath(", c.call, ")")

# --- loadreport -----------------------------------------------------------------------------

const _LR_GROUPS = [
    :member_at_load => "family members fixed at a package's load (a fold kept in its image, checked again: fold_holds)",
    :member_in_fold => "family members fixed in inference (a fold, W-40)",
    :member_at_first_use => "family members fixed or checked at first use (the run-time path, the table)",
    :image_hook => "the image hook (each package image's methods: overrides, strict mode)",
    :package_load => "after each package load (the generation and dynamic candidates, strict mode's validation log)",
    :definition_hook => "the definition hook (each method defined)",
    :definition_check => "definition checks at a trait module's end",
    :first_call_check => "first-call checks of worker signatures",
    :implementation_slow_path => "implementations found by the slow path (generic implementations, dynamic ones)",
    :untyped_table => "the table of declared implementations (untyped calls): first sight of a type",
]
_lr_item(@nospecialize(x)) = x isa Tuple && length(x) == 2 && x[1] isa Type && x[2] isa Type ?
    string(_dshort(x[1], 60), " for ", _dshort(x[2], 70)) : x isa String ? x : _dshort(x, 130)

"""
    loadreport(io = stdout; top = 5)

What TraitWorld's checks and folds cost since the recording started (`JULIA_TW_LOADREPORT=1` when TraitWorld
loads, or `loadreport_switch!(true)`): per step, how often it ran and its time; the slowest items of each
group; the wall-clock and Julia's compile time since the start. Times of nested steps are included in their
group's `total`.
"""
function loadreport(io::IO = stdout; top::Int = 5)
    if _LR_T0[] == 0
        println(io, "loadreport: nothing recorded; set JULIA_TW_LOADREPORT=1 before TraitWorld loads, or call TraitWorld.loadreport_switch!(true)")
        return nothing
    end
    lock(_LR_LOCK)
    parts = copy(_LR_PARTS); items = copy(_LR_ITEMS)
    unlock(_LR_LOCK)
    wall = time_ns() - _LR_T0[]
    ct = Base.cumulative_compile_time_ns()[1] - _LR_CT0[]
    println(io, "TraitWorld load report: ", round(wall / 1e9; digits = 3), " s since the recording started, of it ",
            round(ct / 1e9; digits = 3), " s compiling (Julia's counter)", _LR_ON[] ? "" : "; recording off")
    println(io, "  ", rpad("step", 26), lpad("count", 6), lpad("ms", 10), lpad("compiling", 11))
    any_ = false
    for (g, text) in _LR_GROUPS
        ps = sort!([(p, v) for ((gg, p), v) in parts if gg === g]; by = x -> (x[1] !== :total, -Int(x[2][2])))
        isempty(ps) && continue
        any_ = true
        println(io, "  ", text)
        for (p, v) in ps
            println(io, "    ", rpad(replace(string(p), "_" => " "), 24), lpad(v[1], 6), lpad(v[2] == 0 ? "" : _ms(v[2]), 10),
                    lpad(v[2] == 0 ? "" : _ms(v[3]), 11))
        end
        tot = [(it, ns, cns) for (gg, p, it, ns, cns) in items if gg === g && p === :total]
        isempty(tot) && (tot = [(it, ns, cns) for (gg, p, it, ns, cns) in items if gg === g])
        if length(tot) > 1 && top > 0
            sort!(tot; by = x -> -Int(x[2]))
            println(io, "    slowest (ms, of it compiling):")
            for (it, ns, cns) in tot[1:min(top, end)]
                println(io, "      ", lpad(_ms(ns), 8), lpad(_ms(cns), 8), "  ", _lr_item(it))
            end
        end
    end
    any_ || println(io, "  no step of the machinery ran")
    return nothing
end

# --- Cthulhu (an extension: TraitWorldCthulhuExt, loaded with `using Cthulhu`) ------------------

"""
    descend_facts(f, types; facts = true, kw...)
    descend_facts(callpath(f, args...); kw...)

Cthulhu's interactive descent (`Cthulhu.descend`) over the code compiled by facts for `f(::types...)`, as
`factscode` reads it: each callee in its owner's mode (the facts owner's code by facts). The run-time sites
`factscode` finds and Cthulhu does not list are in the callsite menu as runtime calls. Keywords go to
`Cthulhu.descend`. Needs `using Cthulhu` (the extension `TraitWorldCthulhuExt`).
"""
function descend_facts end
"""
    facts_provider(; facts = true)

The Cthulhu provider of `descend_facts`, for Cthulhu's own entry points
(`Cthulhu.descend(f, types; provider = TraitWorld.facts_provider())`). Needs `using Cthulhu`.
"""
function facts_provider end
