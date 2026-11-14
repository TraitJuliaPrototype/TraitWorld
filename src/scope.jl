# Trait modules (traits §13; lowering §6).

"""
    @trait_module opts...

Before a module's first method: its methods are compiled by facts, an unbounded method at a trait argument
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
        o isa Symbol && (o = Expr(:(=), o, true))        # `bounded` is `bounded = true` (traits §2)
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

The casts in the methods of `mod` and its submodules at an argument that the method the call selects
does not type by a trait (traits §7.6): they have no effect. A package's tests check that it is empty. Listed where inference knows the method a call selects, as
`(method, the method's line, called function's type, argument index)`.
"""
function detect_unused_casts(mod::Module)
    out = Tuple{Method,Int,Any,Int}[]
    for m in _module_methods(mod)
        _has_attributed_call(m) || continue      # only a method whose own code casts is inferred
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

"""
    detect_kept_storage(mod::Module)

The stores in the methods of `mod` and its submodules of a `keep`'s value, or of any `Dynamic{X}`, into
storage typed by the trait: a field `::X`, an element of a `Vector{X}` (traits §7.8, §8.1). Such
storage holds the object at one caller and a box at another; the argument is assigned there without
`keep`, or the storage is typed `Kept{X}`. A package's tests check that it is empty. Listed where the
method is inferred at its declared signature, as `(method, the method's line, the storing function,
the storage's type)`.
"""
function detect_kept_storage(mod::Module)
    out = Tuple{Method,Int,Any,Any}[]
    CC = Core.Compiler
    for m in _module_methods(mod)
        sig = Base.unwrap_unionall(m.sig)
        (sig isa DataType && any(_is_trait_arg, sig.parameters)) || continue
        for (src, _) in (try Base.code_typed_by_type(m.sig; optimize = false) catch; [] end)
            src isa Core.CodeInfo || continue
            # (a query by the signature also gives the more specific methods' code: each at its own)
            (isdefined(src, :parent) && src.parent isa Core.MethodInstance && src.parent.def !== m) && continue
            for st in src.code
                Meta.isexpr(st, :(=)) && (st = st.args[2])
                Meta.isexpr(st, :call) && length(st.args) >= 3 || continue
                ts = Any[CC.widenconst(CC.argextype(a, src, CC.VarState[])) for a in st.args]
                f = CC.singleton_type(CC.argextype(st.args[1], src, CC.VarState[]))
                slot, k = _storage_slot(f, st.args, ts)
                slot === nothing && continue
                _is_trait_arg(slot) || continue
                # the stored value: a `keep`'s result, or a value typed `Dynamic{X}`
                a = st.args[k]
                def = a isa Core.SSAValue ? src.code[a.id] : nothing
                Meta.isexpr(def, :(=)) && (def = def.args[2])
                kept = Meta.isexpr(def, :call) && CC.singleton_type(CC.argextype(def.args[1], src, CC.VarState[])) === Core.keep
                V = ts[k]
                (kept || any(t -> t isa DataType && t <: Dynamic, Base.uniontypes(V))) || continue
                push!(out, (m, Int(m.line), f, slot))
            end
        end
    end
    return unique!(out)
end

# the type of the storage a call writes and the index of the stored value among the call's arguments
# (the function first): a field (`setproperty!`, `setfield!`), an element (`push!`, `pushfirst!`,
# `setindex!`); `(nothing, 0)` for any other call
function _storage_slot(@nospecialize(f), args::Vector{Any}, ts::Vector{Any})
    if (f === setproperty! || f === setfield!) && length(args) >= 4
        T = ts[2]
        name = args[3] isa QuoteNode ? args[3].value : nothing
        T = Base.unwrap_unionall(T)
        (name isa Symbol && T isa DataType && hasfield(T, name)) || return (nothing, 0)
        return (fieldtype(T, name), 4)
    elseif (f === push! || f === pushfirst! || f === setindex!) && length(args) >= 3
        # (a container whose element type names the method's variables, `Vector{X{T}} where T`: the
        # element type with them)
        V = Base.unwrap_unionall(ts[2])
        (V isa DataType && V <: AbstractArray) || return (nothing, 0)
        S = V
        while S.name !== Base.unwrap_unionall(AbstractArray).name
            S = Base.unwrap_unionall(supertype(S))::DataType
        end
        return (S.parameters[1], 3)
    end
    return (nothing, 0)
end

_is_attributed_call(@nospecialize(f)) =
    f === Core.attributed_call || (f isa GlobalRef && f.mod === Core && f.name === :attributed_call)

# Whether a method's lowered code holds a cast's call: inference keeps the statements it does not
# optimize, so only such a method can hold one in its typed code.
function _has_attributed_call(m::Method)
    isdefined(m, :source) && m.source !== nothing || return false
    src = try Base.uncompressed_ir(m) catch; return false end
    for st in src.code
        Meta.isexpr(st, :call) && !isempty(st.args) && _is_attributed_call(st.args[1]) && return true
    end
    return false
end

# A package's own methods: those defined in `mod` or a module defined inside it, at any depth, its
# methods of other modules' functions included (`Base.show(io, ::T)`), so that a package's tests
# check the whole package (traits §7.6; open issue 162).
function _module_methods(mod::Module)
    mods = _own_modules(mod)
    ms = Method[]
    mt = isdefined(Core, :methodtable) ? Core.methodtable : Core.GlobalMethods
    Base.visit(mt) do m
        m isa Method && m.module in mods && push!(ms, m)
    end
    return ms
end

"`mod` and the modules defined inside it, recursively."
function _own_modules(mod::Module)
    out = Module[mod]
    i = 1
    while i <= length(out)
        m = out[i]
        for name in names(m; all = true)
            isdefined(m, name) || continue
            v = getfield(m, name)
            v isa Module && v !== m && parentmodule(v) === m && !(v in out) && push!(out, v)
        end
        i += 1
    end
    return out
end
