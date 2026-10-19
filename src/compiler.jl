# ---------------------------------------------------------------------------
# The facts mode is Julia's (julia-1.13, Compiler/src/facts.jl; writeup/design.md §6): a trait
# module is compiled by facts under the cache owner `:facts` (`@compiler_options facts=true`,
# which `@trait_module` declares), entries are boundaries compiled in their caller's mode
# (`Expr(:meta, :facts_boundary)`), and code compiled by facts dispatches at run time to code compiled
# by facts. What TraitWorld keeps here: the definition checks' interpreter, the world decisions are
# made in, and the facts rule's signature test (the compiler's, one source of truth).
# ---------------------------------------------------------------------------

const CC = Base.Compiler

isdefined(CC, :FACTS_OWNER) ||
    error("TraitWorld needs Julia's facts mode: the patched build in julia-1.13 (stock Julia is not supported)")

"The cache owner of code compiled by facts (Julia's)."
const FACTS_OWNER = CC.FACTS_OWNER

"Whether a signature is a fact: only stakeholders or pirates can change dispatch at it (the compiler's test)."
_fact_sig(@nospecialize(s)) = CC.is_fact_sig(s)
"The concrete signatures a fact signature stands for (its splits), or the signature itself."
function _fact_splits(@nospecialize(s))
    ss = CC.concrete_splits(s)
    return ss === nothing ? Any[s] : ss
end

"""
    @machinery function f(…) … end

A slow path of the machinery (a definition's checks, finding a builder or a family member, the
first call's checks, the definition hooks), compiled by facts whoever calls it (`Expr(:meta,
:facts_always)`, Julia's per-method mode): the code a session compiles for it rests on facts only, so
loading packages does not invalidate it, and strict mode protects it as it protects trait code.
TraitWorld's other code stays plain: the entries' helpers are inlined into plain callers.
"""
macro machinery(ex)
    def = ex
    while def isa Expr && def.head === :macrocall            # `@noinline function …`
        def = def.args[end]
    end
    (def isa Expr && def.head in (:function, :(=))) || error("@machinery: expected a method definition")
    body = def.args[2]
    body isa Expr && body.head === :block || (body = def.args[2] = Expr(:block, body))
    pushfirst!(body.args, Expr(:meta, :facts_always))
    return esc(ex)
end

"The cache owner of the definition checks' inference: none of their results reaches the code that runs."
struct _CheckOwner end
"""
The interpreter of the definition checks (return types, kept trait objects): Julia's native
interpreter with plain inference rules, in a cache of its own, so that checking a worker before any
value exists compiles nothing the program runs. Being Julia's own interpreter, its compiler code
runs in the compiler's world (Base reflection does so for a `NativeInterpreter`): loading packages
never invalidates it. A custom interpreter's compiler code was compiled again after big loads
(3.7 s for a forwarding implementation after CSV, DataFrames and CairoMakie).
"""
_check_interp(world::UInt = Base.get_world_counter()) = CC.NativeInterpreter(world; facts = false, owner = _CheckOwner())
"Keywords for reflection by the definition checks: their own interpreter."
_check_kw(world::UInt = Base.get_world_counter()) = (; world, interp = _check_interp(world))
"""
Keywords for reflection at a signature `sig`: the checks' own cache where it names an archetype (a
worker checked before any value exists, never run); else plain inference in the plain cache, so the
result serves the program's later compilation and reuses what the system image inferred (an
operation's check at a real type inferred Base's broadcasting from scratch: 186 ms per session).
"""
function _check_kw_at(@nospecialize(sig), world::UInt = Base.get_world_counter())
    _names_archetype(sig) && return _check_kw(world)
    return (; world, interp = CC.NativeInterpreter(world; facts = false))
end
"Whether a type mentions an `Archetype` anywhere in its parameters."
function _names_archetype(@nospecialize(T))
    T isa Type || return false
    T = Base.unwrap_unionall(T)
    T isa DataType || return true                       # a union or a variable: undecided, so the checks' own cache
    (T.name === Base.typename(Archetype) || T.name === Base.typename(ParamArchetype)) && return true
    for p in T.parameters
        _names_archetype(p) && return true
    end
    return false
end

"A `CodeInstance`'s inferred result type (as the compiler decodes it: a lattice element may be stored)."
function _ci_return_type(ci::Core.CodeInstance)
    r = CC.cached_return_type(ci)
    return r isa CC.Const ? Core.Typeof(r.val) : CC.widenconst(r)
end

"Print the machinery's slow paths as they run (`JULIA_TW_DEBUG=1`)."
const _FACTS_DEBUG = Ref(false)

"""
    _latest(f, args...)

A slow path of the machinery (finding an implementation's builder, the checks at a signature's first
call), run in the latest world: TraitWorld's own code is plain Julia.
"""
_latest(f, args...) = Base.invokelatest(f, args...)

"""
The world the machinery decides implementations in: the caller's (`tls_world_age()` where an entry's
slow path starts), as plain Julia dispatches in the caller's world. A task pinned to an older world
then sees the implementations of its world, not of the latest. Outside a decision, the latest world.
"""
const _DECISION_WORLD = Base.ScopedValues.ScopedValue{UInt}(UInt(0))
_decision_world() = (w = _DECISION_WORLD[]; w == 0 ? Base.get_world_counter() : w)
_in_decision_world(f, args...) =
    (w = _DECISION_WORLD[]; w == 0 ? Base.invokelatest(f, args...) : Base.invoke_in_world(w, f, args...))
"`_latest` in world `w`, deciding in `w`."
_in_world(w::UInt, f, args...) = Base.ScopedValues.with(_DECISION_WORLD => w) do
    Base.invoke_in_world(w, f, args...)
end
