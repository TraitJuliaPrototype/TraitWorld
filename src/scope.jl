# Trait modules (traits §13; lowering §6).

"""
    @trait_module opts...

Before a module's first method: its methods are compiled by facts (`facts`), an unbounded method at a trait
argument is refused (`bounded`), a pirate is refused (`no_pirates`), and the functions the module neither
exports nor declares `public` take methods from it only (`owner_only`, traits §12.2). All four are on unless
written otherwise (`@trait_module bounded = false`). No option decides how a trait argument is compiled: the
value's type does (traits §7.5, §13). The options are Julia's module options (compiler §2.1).
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
        if Meta.isexpr(o, :(=)) && o.args[1] in (:dynamic, :first_seen)
            error("@trait_module: no option decides how a trait argument is compiled (traits §7.5, §13); got $o. ",
                  "The value's type decides: a library erases at its door, `f(m::Model) = _f(Dynamic{Model}(m))`; ",
                  "a trait whose methods erase every plain member declares `@default_dynamic`; ",
                  "a caller asks for code per type with `compiled_for(x)`")
        end
        (Meta.isexpr(o, :(=)) && o.args[1] isa Symbol && o.args[2] isa Bool &&
         o.args[1] in (:facts, :bounded, :no_pirates, :owner_only)) ||
            error("@trait_module: an option is facts, bounded, no_pirates or owner_only = true or false; got $o")
        given[o.args[1]] = o.args[2]
    end
    settings = Any[Expr(:(=), k, get(given, k, true)) for k in (:facts, :bounded, :no_pirates, :owner_only)]
    fully_typed === nothing || push!(settings, Expr(:(=), :fully_typed, fully_typed))
    return esc(Expr(:macrocall, GlobalRef(Base.Experimental, Symbol("@compiler_options")),
                    __source__, settings...))
end

# a trait argument's type, as the compiler reads it (compiler §6.3): a set, or an intersection of sets
_is_trait_arg(@nospecialize(t)) = ccall(:jl_is_trait_arg_type, Cint, (Any,), t) != 0

