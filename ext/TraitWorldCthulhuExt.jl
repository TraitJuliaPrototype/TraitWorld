# Cthulhu's descent over the code compiled by facts (W-85): a provider of Cthulhu 3 whose code comes from
# Julia's native interpreter in the facts mode, as `factscode` reads it, each callee in its own owner's mode
# (a method of the facts owner by facts, plain code plainly). Run-time sites `factscode` finds that Cthulhu
# does not list (a split's last branch, a call through a pointer, a dispatch at an abstract signature) are
# added to the callsite menu as Cthulhu's runtime calls, labelled as `factscode` labels them.
module TraitWorldCthulhuExt

using TraitWorld
using Cthulhu
using Core: CodeInstance, MethodInstance, CodeInfo

const CC = Base.Compiler
const CH = Cthulhu.get_module_for_compiler_integration(; use_compiler_stdlib = false)

"""
The facts provider: the facts interpreter `factscode` uses (`facts = false`: plain inference), and the
code it made for each code instance, optimized and not.
"""
struct FactsProvider <: Cthulhu.AbstractProvider
    interp::CC.NativeInterpreter
    opt::IdDict{CodeInstance,Any}
    unopt::IdDict{CodeInstance,Any}
end
function FactsProvider(; facts::Bool = true, world::UInt = Base.get_world_counter())
    nat = CC.NativeInterpreter(world)
    return FactsProvider(facts ? CC.facts_interp(nat) : nat, IdDict{CodeInstance,Any}(), IdDict{CodeInstance,Any}())
end
TraitWorld.facts_provider(; kw...) = FactsProvider(; kw...)

Cthulhu.get_abstract_interpreter(p::FactsProvider) = p.interp
"The interpreter of a code instance's owner: the facts owner's code by facts, any other plainly."
_interp_of(p::FactsProvider, ci::CodeInstance) = ci.owner === CC.FACTS_OWNER ? CC.facts_interp(p.interp) : CC.plain_interp(p.interp)

CH.run_type_inference(p::FactsProvider, interp::CC.NativeInterpreter, mi::MethodInstance) =
    CC.typeinf_ext(interp, mi, CC.SOURCE_MODE_GET_SOURCE)::CodeInstance

function CH.OptimizedSource(p::FactsProvider, ::CC.NativeInterpreter, ci::CodeInstance)
    return get!(p.opt, ci) do
        ir, _ = CC.typeinf_ircode(_interp_of(p, ci), CC.get_ci_mi(ci), nothing)
        ir === nothing && error("TraitWorld: $(CC.get_ci_mi(ci)) could not be inferred again")
        CH.OptimizedSource(ir, CH.ir_to_src(ir), false, CH.get_effects(ci))
    end
end
function CH.InferredSource(p::FactsProvider, ::CC.NativeInterpreter, ci::CodeInstance)
    return get!(p.unopt, ci) do
        frame = CC.typeinf_frame(_interp_of(p, ci), CC.get_ci_mi(ci), false)
        frame === nothing && error("TraitWorld: $(CC.get_ci_mi(ci)) could not be inferred again")
        CH.InferredSource(copy(frame.src), collect(Any, frame.stmt_info), frame.ipo_effects, frame.result.result, frame.result.exc_result)
    end
end
# the code instance in the facts owner's cache keeps no optimized source (its owner discards it): the code is
# inferred again here, by the owner's interpreter, for both views
function CH.lookup(p::FactsProvider, interp::CC.NativeInterpreter, ci::CodeInstance, optimize::Bool)
    rt, exct, effects = CH.cached_return_type(ci), CH.cached_exception_type(ci), CH.get_effects(ci)
    if optimize
        opt = CH.OptimizedSource(p, interp, ci)
        ir = copy(opt.ir)
        infos = collect(Any, ir.stmts.info)
        for (i, st) in enumerate(ir.stmts.stmt)       # an invoke without its call's info: Cthulhu descends by its code instance
            Meta.isexpr(st, :invoke) && infos[i] === CC.NoCallInfo() && (infos[i] = nothing)
        end
        return CH.LookupResult(ir, opt.src, rt, exct, infos, ir.argtypes, effects, true)
    end
    unopt = CH.InferredSource(p, interp, ci)
    src = copy(unopt.src)
    slottypes = something(src.slottypes, Any[Any for _ in 1:length(src.slotflags)])
    return CH.LookupResult(nothing, src, unopt.rt, unopt.exct, unopt.stmt_info, slottypes, unopt.effects, false)
end

# per-statement remarks, effects and exception types are not kept: the toggles show nothing
Cthulhu.get_pc_remarks(::FactsProvider, ::CodeInstance) = nothing
Cthulhu.get_pc_effects(::FactsProvider, ::CodeInstance) = nothing
Cthulhu.get_pc_excts(::FactsProvider, ::CodeInstance) = nothing
# a constant-propagated callee is shown as its code instance (the native interpreter keeps no source for it)
Cthulhu.get_override(::FactsProvider, ::CH.ConstPropCallInfo) = nothing

# the facts mode's call infos (Compiler/src/facts.jl): a split is its call at the candidates; a fold, a constant
CH.process_info(p::FactsProvider, result::CH.LookupResult, info::CC.SplitCallInfo, argtypes::CH.ArgTypes,
                @nospecialize(rt), @nospecialize(exct), effects::Union{CC.Effects,Nothing}) =
    CH.process_info(p, result, info.info, argtypes, rt, exct, effects)
CH.process_info(::FactsProvider, ::CH.LookupResult, ::CC.FoldCallInfo, ::CH.ArgTypes,
                @nospecialize(rt), @nospecialize(exct), ::Union{CC.Effects,Nothing}) = CH.CallInfo[]

"Short labels for the callsite menu (its lines are cut at the terminal's width)."
const _SHORT_KIND = Dict(:dispatch => "dispatch", :split_table => "split table", :pointer => "pointer",
                         :apply => "apply", :latest => "latest world", :error => "not inferred")
const _SHORT_NOTE = Dict("an error path" => "error", "the first-call check: once per signature" => "first call",
                         "first sight of a type at a table" => "first sight", "a family member's first use" => "first use",
                         "only for a result like the input" => "like-input result",
                         "the untyped fallback: a value without the traits" => "fallback",
                         "first sight of a dynamic value's type" => "first sight")

"A site's call for the menu: a split's call without its candidates (`factscode` lists them)."
_menu_call(s) = s.kind === :split_table ? first(split(s.call, "(::<a type outside")) : s.call
"""
A site's result type: for a split table's lookup, the type of the call through the pointer it returns (the
statement that calls it), else the statement's own.
"""
function _site_rt(src::CodeInfo, i::Int)
    st = src.code[i]
    if Meta.isexpr(st, :foreigncall) && TraitWorld._fc_name(st.args[1]) === :jl_split_table_ptr
        for j in (i + 1):min(i + 8, length(src.code))
            u = src.code[j]
            Meta.isexpr(u, :foreigncall) && u.args[1] == Core.SSAValue(i) && return CC.widenconst(src.ssavaluetypes[j])
        end
    end
    return CC.widenconst(src.ssavaluetypes[i])
end

"""
The callsites Cthulhu finds, and the run-time sites `factscode` finds at statements Cthulhu does not list,
as runtime calls (not descended into), in statement order.
"""
function CH.find_callsites(p::FactsProvider, result::CH.LookupResult, ci::CodeInstance, annotate_source::Bool = false,
                           pc2excts::Union{Nothing,CH.PC2Excts} = nothing)
    callsites, nodes = invoke(CH.find_callsites, Tuple{Cthulhu.AbstractProvider,CH.LookupResult,CodeInstance,Bool,Union{Nothing,CH.PC2Excts}},
                              p, result, ci, annotate_source, pc2excts)
    (result.optimized && result.src isa CodeInfo) || return callsites, nodes
    at = Dict{Int,Int}(c.id => k for (k, c) in enumerate(callsites))
    sites, _ = TraitWorld._ir_sites(result.src, "")
    added = false
    for s in sites
        tag = string("[", get(_SHORT_KIND, s.kind, string(s.kind)), isempty(s.note) ? "" : string(", rare: ", get(_SHORT_NOTE, s.note, s.note)), "] ")
        k = get(at, s.stmt, 0)
        if k > 0
            # Cthulhu's own runtime call: named as `factscode` names it (a callee behind a barrier, a rare path)
            c = callsites[k]
            if c.info isa CH.RTCallInfo && !isempty(s.fname)
                callsites[k] = CH.Callsite(c.id, CH.RTCallInfo(tag * s.fname, c.info.argtyps, c.info.rt, c.info.exct), c.head)
                annotate_source && length(nodes) == length(callsites) && nodes[k] isa CH.Callsite && (nodes[k] = callsites[k])
            end
            continue
        end
        cs = CH.Callsite(s.stmt, CH.RTCallInfo(tag * _menu_call(s), Any[], _site_rt(result.src, s.stmt), nothing), :call)
        push!(callsites, cs)
        annotate_source && push!(nodes, cs)
        at[s.stmt] = length(callsites)
        added = true
    end
    if added
        perm = sortperm(callsites; by = c -> c.id)
        callsites = callsites[perm]
        annotate_source && length(nodes) == length(perm) && (nodes = nodes[perm])
    end
    return callsites, nodes
end

function TraitWorld.descend_facts(@nospecialize(f), @nospecialize(types = Base.default_tt(f)); facts::Bool = true, kw...)
    return Cthulhu.descend(f, types; provider = FactsProvider(; facts), kw...)
end
TraitWorld.descend_facts(c::TraitWorld.CallPath; kw...) =
    c.worker_sig === nothing ? error("callpath found no worker for $(c.call)") :
    TraitWorld.descend_facts(c.worker_sig.parameters[1].instance, Tuple{c.worker_sig.parameters[2:end]...}; kw...)

end
