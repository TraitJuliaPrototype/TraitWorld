# Trait modules (traits §13; lowering §6).

"""
    @trait_module opts...

Before a module's first method: its methods are compiled by facts, an open method at a trait argument
is refused (`bounded`), a pirate is refused (`no_pirates`), and where nothing else decides, a trait
argument's attribute is what the caller knows (`first_seen`). All four are on unless written
otherwise (`@trait_module bounded = false`); `dynamic = true` makes every trait argument of the
module's methods `Dynamic` by default. The options are Julia's module options (compiler §2.1).
"""
macro trait_module(opts...)
    given = Dict{Symbol,Bool}()
    fully_typed = nothing
    for o in opts
        if Meta.isexpr(o, :(=)) && o.args[1] === :fully_typed && o.args[2] isa QuoteNode
            fully_typed = o.args[2].value      # from @enforce_fully_typed or @warn_not_fully_typed (traits §14)
            continue
        end
        (Meta.isexpr(o, :(=)) && o.args[1] isa Symbol && o.args[2] isa Bool &&
         o.args[1] in (:facts, :bounded, :no_pirates, :dynamic, :first_seen)) ||
            error("@trait_module: an option is facts, bounded, no_pirates, dynamic or first_seen = true or false; got $o")
        given[o.args[1]] = o.args[2]
    end
    settings = Any[Expr(:(=), k, get(given, k, k !== :dynamic))
                   for k in (:facts, :bounded, :no_pirates, :dynamic, :first_seen)]
    fully_typed === nothing || push!(settings, Expr(:(=), :fully_typed, fully_typed))
    return esc(Expr(:macrocall, GlobalRef(Base.Experimental, Symbol("@compiler_options")),
                    __source__, settings...))
end

# a trait argument's type, as the compiler reads it (compiler §6.3): a set, or an intersection of sets
_is_trait_arg(@nospecialize(t)) = ccall(:jl_is_trait_arg_type, Cint, (Any,), t) != 0

"""
    detect_dynamic_fallbacks(mod::Module)

The trait arguments of `mod`'s methods that the scope's fallback makes `Dynamic` where the caller does
not know the value's type (traits §7.5, step 5; §14): in a trait module (`first_seen`), each trait
argument for which nothing stronger decides, neither the method's `@nospecialize` or `@specialize`,
the module's `dynamic`, nor the trait's default. As `(method, argument index, line)`.
"""
function detect_dynamic_fallbacks(mod::Module)
    out = Tuple{Method,Int,Int}[]
    for m in _module_methods(mod)
        opts = ccall(:jl_get_module_trait_options, Cint, (Any,), m.module)
        (opts & 8) != 0 && (opts & 4) == 0 || continue
        sig = Base.unwrap_unionall(m.sig)
        sig isa DataType || continue
        for i in 2:min(length(sig.parameters), 33)
            d = sig.parameters[i]
            _is_trait_arg(d) || continue
            bit = UInt32(1) << (i - 2)
            (m.nospecialize & bit) != 0 && continue
            (m.specialize & bit) != 0 && continue
            ccall(:jl_get_default_attribute, Cint, (Any,), d) != 0 && continue
            push!(out, (m, i - 1, Int(m.line)))
        end
    end
    return out
end

"""
    detect_unused_casts(mod::Module)

The casts in `mod`'s methods at an argument that the method the call selects does not type by a trait
(traits §7.6): they have no effect. Listed where inference knows the method a call selects, as
`(method, the method's line, called function's type, argument index)`.
"""
function detect_unused_casts(mod::Module)
    out = Tuple{Method,Int,Any,Int}[]
    for m in _module_methods(mod)
        for (src, _) in (try Base.code_typed_by_type(m.sig; optimize = false) catch; [] end)
            src isa Core.CodeInfo || continue
            for st in src.code
                Meta.isexpr(st, :call) && length(st.args) >= 3 || continue
                _is_attributed_call(st.args[1]) || continue
                bits = st.args[2]
                bits isa Int || continue
                mask = UInt32(bits & 0xffffffff)
                argtypes = Any[Core.Compiler.widenconst(Core.Compiler.argextype(a, src, Core.Compiler.VarState[])) for a in st.args[3:end]]
                ms = try Base._methods_by_ftype(Tuple{argtypes...}, 1, Base.get_world_counter()) catch; nothing end
                (ms isa Vector && length(ms) == 1) || continue
                callee = (ms[1]::Core.MethodMatch).method
                csig = Base.unwrap_unionall(callee.sig)
                csig isa DataType || continue
                for k in 1:min(32, length(argtypes) - 1)
                    (mask & (UInt32(1) << (k - 1))) != 0 || continue
                    k + 1 <= length(csig.parameters) && _is_trait_arg(csig.parameters[k + 1]) && continue
                    push!(out, (m, Int(m.line), argtypes[1], k))
                end
            end
        end
    end
    return out
end

_is_attributed_call(@nospecialize(f)) =
    f === Core.attributed_call || (f isa GlobalRef && f.mod === Core && f.name === :attributed_call)

function _module_methods(mod::Module)
    ms = Method[]
    for name in names(mod; all = true)
        isdefined(mod, name) || continue
        f = getfield(mod, name)
        (f isa Function || f isa Type) || continue
        for m in methods(f)
            m.module === mod && push!(ms, m)
        end
    end
    return ms
end
