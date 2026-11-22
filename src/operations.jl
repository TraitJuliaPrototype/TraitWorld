# `operations(x)`: what can be done with a value, read from the contracts (W-150; traits §15). For each trait the
# value's type is a member of, its operations as the contract writes them, its declared fields and the methods at
# the trait; then the methods at the value's own type. A function a user calls at the prompt, not a hook: its entry
# is a run-time site (runtime.jl), and the library's image compiles none of it.

"""
One line of [`operations`](@ref): an operation as its contract writes it (`area(s::Shape)::Float64`), a declared
field (`@const name::String`), or a method as its signature is written (`ratio(s::Shape)`). `note` is `"a default"`
for an operation with a default; `doc` the first line of the docstring, where there is one; `method` the method, for a
method's line.
"""
struct OperationLine
    text::String
    note::String
    doc::String
    method::Union{Method,Nothing}
end

"""
One trait's group in [`operations`](@ref): the trait (bare; an intersection `All{X, Y}` for the methods at it), its
instance at the subject's parameters where known, how the subject is a member (`via`), the first line of the trait's
docstring, the contract's operations and declared fields, and the methods at the trait. `reached` is false for a
trait whose operations do not reach the object through a box.
"""
struct TraitOperations
    trait::Any
    instance::Any
    via::String
    doc::String
    operations::Vector{OperationLine}
    fields::Vector{OperationLine}
    methods::Vector{OperationLine}
    reached::Bool
end

"""
    Operations

What [`operations`](@ref) returns: `subject` (the value or type as printed), `kind` (`:value`, `:type`, `:box`,
`:wrapper`, `:trait`, `:boxtype` for the box's type), `type` (the type whose operations are listed: the object's for a box or a wrapper), `istrait`, `note` (what a box or a wrapper hides; a function's
signatures), `traits` (one [`TraitOperations`](@ref) a trait, in the order printed), `members` (a trait's declared
members), `other` (the methods at the type itself, at most the bound) and `more` (how many of those are not listed).
"""
struct Operations
    subject::String
    kind::Symbol
    type::Any
    istrait::Bool
    note::String
    traits::Vector{TraitOperations}
    members::Vector{String}
    other::Vector{OperationLine}
    more::Int
end

"""
    operations(x; limit = 12)
    operations(T::Type; limit = 12)

The operations available on the value `x`, or on a value of the type `T`, grouped by trait. For each trait the type is
a member of (by its own membership, a supertrait, forwarding with `by`, or an abstract type that is a member): the
operations as the contract writes them, with their declared results, defaults and the first line of their docstrings;
the declared fields; the methods at the trait. Then the methods at the type itself that no trait lists, at most
`limit` of them, with the count of the rest. `Callable` is not listed for a function: every function is a member of
every signature its methods take.

For a trait `X`, `operations(X)` gives its contract, its supertraits' and its declared members. For a box or a
wrapper, the operations of the object it holds, and what the kept form hides: through a box only the operations of
its trait and its supertraits reach the object; through either, a method at the object's own type needs `unwrap(x)`.

The result prints grouped, one operation a line; its fields are for tools and tests (`Operations`). At the REPL,
`TraitWorld.install_operations_key!()` binds Alt-o to it, on the word under the cursor.
"""
operations(@nospecialize(x); limit::Int = 12) = _runtime_site(_operations, x, limit, "")::Operations

const _ALL_NAME = Base.unwrap_unionall(Core.All).name
_is_all(@nospecialize(T)) = (u = Base.unwrap_unionall(T); u isa DataType && u.name === _ALL_NAME)
_is_kept_name(tn::Core.TypeName) =
    tn === Base.unwrap_unionall(Dynamic).name || tn === Base.unwrap_unionall(Compiled).name

# a type or a value as Julia prints it at the prompt: module prefixes only where a name is not visible from Main
_shown(@nospecialize(x)) = sprint(show, x; context = (:module => Main, :limit => true))
_clip(s::AbstractString, n::Int) = length(s) <= n ? String(s) : string(first(s, n - 1), "…")
_names_kept_form(s::AbstractString) = occursin("Dynamic{", s) || occursin("Compiled{", s)

# A type as the listing names it: as Julia prints it, or its name with `{…}` where that would be long or would show a
# kept form the user did not write (a problem whose type holds the box a library made of a function)
function _type_label(@nospecialize(T))
    s = _shown(T)
    u = Base.unwrap_unionall(T)
    (length(s) > 48 || _names_kept_form(s)) && u isa DataType && return string(_shown(u.name.wrapper), "{…}")
    return s
end
# a value as the listing names it: as Julia prints it, where short and without a kept form inside; else nothing
function _value_label(@nospecialize(x))
    s = _shown(x)
    return length(s) > 48 || _names_kept_form(s) ? "" : s
end
_article(s::AbstractString) = (!isempty(s) && lowercase(first(s)) in ('a', 'e', 'i', 'o', 'u')) ? "an " : "a "

function _operations(@nospecialize(x), limit::Int, name::String)
    if x isa Type
        (istrait(x) || _is_all(x)) && return _trait_operations(x)
        u = Base.unwrap_unionall(x)
        if u isa DataType && u.name === Base.unwrap_unionall(Dynamic).name && !isempty(u.parameters) && u.parameters[1] isa Type
            X = u.parameters[1]
            note = "the box: only the operations and declared fields of $(_shown(bare(X))) and its supertraits reach the object it holds"
            return _subject_operations(_type_label(x), X, X, :boxtype, note, limit)
        elseif u isa DataType && u.name === Base.unwrap_unionall(Compiled).name && !isempty(u.parameters) && u.parameters[1] isa Type
            S = u.parameters[1]
            return _subject_operations(_type_label(x), S, x, :wrapper, _wrapper_note(S), limit)
        end
        return _subject_operations(_type_label(x), x, nothing, :type, "", limit)
    end
    # a kept form the user made is named as Julia prints it
    subject = !isempty(name) ? name : x isa Union{Dynamic,Compiled} ? (s = _shown(x); length(s) <= 48 ? s : "") : _value_label(x)
    if x isa Dynamic
        X = typeof(x).parameters[1]
        S = typeof(unwrap(x))
        note = "the box: only the operations and declared fields of $(_shown(bare(X))) and its supertraits reach the " *
               "$(_type_label(S)) it holds; the rest needs unwrap(x)"
        return _subject_operations(subject, S, X, :box, note, limit)
    elseif x isa Compiled
        S = typeof(unwrap(x))
        return _subject_operations(subject, S, nothing, :wrapper, _wrapper_note(S), limit)
    end
    note = x isa Function ? "a function: a member of each `Callable{A, S}` whose arguments `A` its methods take " *
                            "(`methods($(_shown(x)))`)" : ""
    return _subject_operations(subject, typeof(x), nothing, :value, note, limit)
end

_wrapper_note(@nospecialize(S)) = "the wrapper: a member of each trait of the $(_type_label(S)) it holds, compiled for it; " *
                                  "a method at $(_type_label(S)) itself needs unwrap(x)"

# The traits `T` is a member of, each with how: its own membership, by a field, as an abstract type that is a member,
# through a subtrait. The entries in force on its TypeName and its supertypes', then the sets those join.
function _memberships(@nospecialize(T))
    out = Tuple{Any,String}[]
    d = Base.unwrap_unionall(T)
    own = d isa DataType ? d.name : nothing
    while d isa DataType && d !== Any
        for en in getfield(d.name, :memberships, :acquire)
            getfield(en, :max_world, :acquire) == typemax(UInt64) || continue
            sn = getfield(en, :set)
            X = sn.wrapper
            T <: X || continue
            _has_trait(out, X) && continue
            by = getfield(en, :by)
            via = by isa Symbol && getfield(en, :receiver) === :field && !_is_kept_name(d.name) ? "by the field `$by`" :
                  d.name !== own ? "as $(_shown(getfield(en, :member)))" : ""
            push!(out, (X, via))
            _supertraits!(out, X, T)
        end
        d = d.super
    end
    return out
end
function _supertraits!(out, @nospecialize(X), @nospecialize(T), depth::Int = 0)
    depth > 8 && return out
    for en in getfield(Base.unwrap_unionall(X).name, :memberships, :acquire)
        getfield(en, :max_world, :acquire) == typemax(UInt64) || continue
        S = getfield(en, :set).wrapper
        (T === nothing || T <: S) || continue
        _has_trait(out, S) && continue
        push!(out, (S, "through $(_shown(bare(X)))"))
        _supertraits!(out, S, T, depth + 1)
    end
    return out
end
function _has_trait(out, @nospecialize(X))
    for (Y, _) in out
        Y === X && return true
    end
    return false
end

function _subject_operations(subject::String, @nospecialize(S), @nospecialize(box), kind::Symbol, note::String, limit::Int)
    if kind === :boxtype
        # the box's type: its trait and its supertraits, nothing of an object
        X = box
        ms = Tuple{Any,String}[(bare(X), "")]
        _supertraits!(ms, bare(X), nothing)
        S = nothing
    else
        ms = _memberships(S)
    end
    # a function's `Callable` is listed only where asked, `operations(Callable)`
    kind in (:box, :boxtype) || filter!(m -> m[1] !== Core.Callable, ms)
    home = S === nothing ? nothing : (u = Base.unwrap_unionall(S); u isa DataType ? u.name.module : nothing)
    sort!(ms; by = m -> (parentmodule(m[1]) === home ? 0 : 1, string(nameof(m[1]))))
    reached = Set{Any}()
    if kind === :box
        push!(reached, bare(box))
        for (Y, _) in _supertraits!(Tuple{Any,String}[], bare(box), nothing)
            push!(reached, Y)
        end
    end
    traits = Any[m[1] for m in ms]
    at, alls, other = _scan_methods(S, traits, home)
    groups = TraitOperations[]
    for (X, via) in ms
        inst = S === nothing ? (kind === :boxtype ? box : X) : _instance_or(X, S)
        push!(groups, _group(X, inst, via, get(at, X, Method[]), kind !== :box || X in reached))
    end
    for (A, mths) in alls
        push!(groups, TraitOperations(A, A, "", "", OperationLine[], OperationLine[], _method_lines(mths, nothing), kind !== :box))
    end
    # the methods at the type itself, without the members' methods of the operations listed above
    opf = Set{Any}()
    for X in traits
        c = contract(X)
        c === nothing && continue
        for op in c.operations
            push!(opf, op.f)
        end
    end
    filter!(m -> (f = _method_function(m); f !== nothing && !(f in opf) && _visible_function(f, home)), other)
    sort!(other; by = m -> (m.module === home || m.module === Main ? 0 : Base.moduleroot(m.module) === Base ? 1 : 2,
                            string(m.name), string(m.file), m.line))
    shown = other[1:min(limit, length(other))]
    return Operations(subject, kind, S === nothing ? box : S, false, note, groups, String[], _method_lines(shown, nothing; sorted = true),
                      length(other) - length(shown))
end

_method_function(m::Method) = (ft = Base.unwrap_unionall(m.sig).parameters[1]; ft isa DataType && isdefined(ft, :instance) ? ft.instance : nothing)

# A function the listing names: one a user can call by name, public in its module (exported or declared `public`), or
# of `Main` or of a module in `homes` (the subject's, the trait's); not a name that starts with `_` or `@` (a module's
# own, a macro)
function _visible_function(@nospecialize(f), homes...)
    f isa Function || return false
    nm = nameof(f)
    s = string(nm)
    (startswith(s, "_") || startswith(s, "@") || startswith(s, "#")) && return false
    fm = typeof(f).name.module
    return fm === Main || any(h -> h === fm, homes) || Base.ispublic(fm, nm)
end

function _instance_or(@nospecialize(X), @nospecialize(S))
    isempty(Base.unwrap_unionall(X).parameters) && return X
    inst = try _instance_at(X, S) catch; nothing end
    return inst === nothing ? X : inst
end

function _trait_operations(@nospecialize(X))
    comps = _is_all(X) ? _components(X) : Any[X]
    ms = Tuple{Any,String}[]
    for C in comps
        _has_trait(ms, bare(C)) || push!(ms, (bare(C), ""))
        _supertraits!(ms, bare(C), nothing)
    end
    at, _, _ = _scan_methods(nothing, Any[m[1] for m in ms])
    groups = TraitOperations[]
    for (Y, via) in ms
        push!(groups, _group(Y, Y === bare(X) ? X : Y, via, get(at, Y, Method[]), true))
    end
    members = String[]
    if !_is_all(X)
        # every member pattern in force: a type, a family, an abstract type, a trait (compiler §7.6)
        for M in ccall(:jl_set_member_patterns, Any, (Any,), bare(X))::Vector{Any}
            u = Base.unwrap_unionall(M)
            u isa DataType && _is_kept_name(u.name) && continue
            # a family over all its parameters by its name: `ODEProblem` for `ODEProblem{T, P, F, J} where {T, P, F, J}`
            whole = M isa UnionAll && u isa DataType && all(p -> p isa TypeVar, u.parameters)
            s = whole ? _shown(u.name.wrapper) : _shown(M)
            s in members || push!(members, s)
        end
    end
    n = length(members)
    note = _is_all(X) ? "an intersection: a member of each of " * join((_shown(bare(C)) for C in comps), ", ") :
           "a trait with $(n == 0 ? "no" : n) declared member$(n == 1 ? "" : "s")"
    return Operations(_shown(X), :trait, X, true, note, groups, members, OperationLine[], 0)
end

# one trait's group: the contract's operations and fields as written, and the methods at the trait
function _group(@nospecialize(X), @nospecialize(inst), via::String, mths::Vector{Method}, reached::Bool)
    c = contract(X)
    ops = OperationLine[]
    fields = OperationLine[]
    if c !== nothing
        for op in c.operations
            push!(ops, OperationLine(_written_op(op), op.hasdefault ? "a default" : "", _op_doc(op, X), nothing))
        end
        for f in c.fields
            push!(fields, OperationLine(string(f.isconst ? "@const " : "", f.name, "::", f.type), "", "", nothing))
        end
    end
    return TraitOperations(X, inst, via, _binding_doc(X), ops, fields, _method_lines(mths, X), reached)
end

# an operation as its contract writes it: `area(s::Shape)::Float64`, `get(d::Keyed, k::K, default::D)::Union{V, D} where {D}`
function _written_op(op::OperationDecl)
    parts = String[]
    for (i, (n, ty)) in enumerate(op.args)
        nm = startswith(string(n), "#") ? "" : string(n)
        a = ty === nothing ? nm : string(nm, "::", ty)
        op.vararg && i == length(op.args) && (a *= "...")
        push!(parts, a)
    end
    w = isempty(op.wherevars) ? "" : " where {" * join((string(v) for v in op.wherevars), ", ") * "}"
    return string(op.name, "(", join(parts, ", "), ")::", op.result, w)
end

# One walk over every method: those at one of `traits` (at an argument the subject's type can be passed at), those at
# an intersection the subject is in, and those at the subject's own type (its TypeName, at parameters it has).
function _scan_methods(@nospecialize(S), traits::Vector{Any}, home = nothing)
    at = IdDict{Any,Vector{Method}}()
    alls = IdDict{Any,Vector{Method}}()
    other = Method[]
    u = S === nothing ? nothing : Base.unwrap_unionall(S)
    own = u isa DataType ? u.name : nothing
    Base.visit(Core.methodtable) do m
        m isa Method || return
        _classify_method!(at, alls, other, m, S, own, traits)
    end
    for (X, v) in at
        filter!(m -> !_is_trait_method(m) && _visible_function(_method_function(m), parentmodule(X), home), v)
    end
    for (_, v) in alls
        filter!(m -> _visible_function(_method_function(m), home), v)
    end
    filter!(p -> !isempty(p.second), alls)
    return at, sort!(collect(alls); by = p -> _shown(p.first)), other
end

function _classify_method!(at, alls, other, m::Method, @nospecialize(S), own, traits::Vector{Any})
    sig = Base.unwrap_unionall(m.sig)
    sig isa DataType || return
    ps = sig.parameters
    length(ps) >= 2 || return
    startswith(string(m.name), "#") && return              # a closure, a keyword method's body
    ps[1] === typeof(Core.kwcall) && return
    m.module === TraitWorld && startswith(string(m.name), "_") && return
    # Core's and the compiler's own methods (its copies of Base's functions): the machinery's, not a user's
    (m.module === Core || nameof(Base.moduleroot(m.module)) === :Compiler || nameof(m.module) === :Compiler) && return
    _names_kept(ps) && return                               # a kept form's method: the machinery's
    for i in 2:length(ps)
        p = ps[i]
        Base.isvarargtype(p) && (p = p.T)
        for c in _alternatives(p)
            cu = Base.unwrap_unionall(c)
            cu isa DataType || continue
            if istrait(cu)
                X = cu.name.wrapper
                _in_by_identity(X, traits) || continue
                (S === nothing || S <: Base.rewrap_unionall(c, m.sig)) || continue
                push!(get!(Vector{Method}, at, X), m)
                return
            elseif cu.name === _ALL_NAME
                S === nothing && continue
                A = Base.rewrap_unionall(c, m.sig)
                S <: A || continue
                key = nothing
                for k in keys(alls)
                    k == cu && (key = k)
                end
                push!(get!(Vector{Method}, alls, key === nothing ? cu : key), m)
                return
            elseif own !== nothing && cu.name === own
                S <: Base.rewrap_unionall(c, m.sig) || continue
                push!(other, m)
                return
            end
        end
    end
end

# the type an argument's declaration names: itself, or a variable's bound. A union names none of its members: a
# method at `Union{Nothing, String}` is no method at `String` here, as for `methodswith`
function _alternatives(@nospecialize(p))
    p isa TypeVar && (p = p.ub)
    return Any[p]
end
function _names_kept(ps)
    for p in ps
        Base.isvarargtype(p) && (p = p.T)
        p isa TypeVar && (p = p.ub)
        for c in (p isa Union ? Base.uniontypes(p) : Any[p])
            cu = Base.unwrap_unionall(c)
            cu isa DataType && _is_kept_name(cu.name) && return true
        end
    end
    return false
end

# methods as their signatures are written, in the order they are defined in (by file and line); keywords by name
function _method_lines(ms::Vector{Method}, @nospecialize(X); sorted::Bool = false)
    home = X === nothing ? nothing : parentmodule(X)
    v = sorted ? ms : sort(ms; by = m -> (m.module === home ? 0 : 1, string(m.file), m.line))
    out = OperationLine[]
    for m in v
        t = try strip(_written_method(m), '`') catch; string(m.name, "(…)") end
        kws = try Base.kwarg_decl(m) catch; Symbol[] end
        if !isempty(kws) && !occursin(';', t)
            head, wh = occursin(" where ", t) ? split(t, " where "; limit = 2) : (t, "")
            j = findlast(')', head)
            j === nothing || (t = string(head[1:prevind(head, j)], "; ", join(kws, ", "), head[j:end], isempty(wh) ? "" : " where " * wh))
        end
        any(l -> l.text == t, out) && continue
        push!(out, OperationLine(String(t), "", "", m))
    end
    return out
end

# The first line of a docstring: its first line of prose, not the signature block above it
function _first_line(s::AbstractString)
    for l in eachsplit(s, '\n')
        startswith(l, "    ") && continue
        t = strip(l)
        (isempty(t) || startswith(t, "```") || startswith(t, "#")) && continue
        return _clip(t, 64)
    end
    return ""
end

# the docstrings of a binding, from every module that documents it: (signature, text)
function _docs_of(mod::Module, name::Symbol)
    out = Tuple{Any,String}[]
    b = try Base.Docs.Binding(mod, name) catch; return out end
    for dm in Base.Docs.modules
        md = get(Base.Docs.meta(dm), b, nothing)
        md isa Base.Docs.MultiDoc || continue
        for (sig, ds) in md.docs
            ds isa Base.Docs.DocStr || continue
            text = join((t for t in ds.text if t isa AbstractString), "")
            push!(out, (sig, text))
        end
    end
    return out
end

_binding_doc(@nospecialize(X)) = (u = Base.unwrap_unionall(X); u isa DataType ?
    _pick_doc(_docs_of(u.name.module, u.name.name), nothing) : "")

# An operation's docstring: the one at a signature that names the trait; else the function's own (written for no
# signature); else the only one. For another owner's function (Base's `length`), the function's own.
function _op_doc(op::OperationDecl, @nospecialize(X))
    f = op.f
    f isa Function || return ""
    mt = typeof(f).name
    return _pick_doc(_docs_of(mt.module, nameof(f)), X)
end
function _pick_doc(docs::Vector{Tuple{Any,String}}, @nospecialize(X))
    isempty(docs) && return ""
    if X !== nothing
        for (sig, text) in docs
            u = Base.unwrap_unionall(sig)
            # `@doc`'s form of a signature with `where` variables is a union of tuples
            for t in (u isa Union ? Base.uniontypes(u) : Any[u])
                t isa DataType && t <: Tuple || continue
                for p in t.parameters
                    pu = Base.unwrap_unionall(p isa TypeVar ? p.ub : p)
                    pu isa DataType && pu.name === Base.unwrap_unionall(X).name && return _first_line(text)
                end
            end
        end
    end
    for (sig, text) in docs
        sig === Union{} && return _first_line(text)
    end
    return length(docs) == 1 ? _first_line(docs[1][2]) : ""
end

# --- printing -----------------------------------------------------------------------------------------------------

function Base.show(io::IO, ops::Operations)
    print(io, "Operations(", ops.subject, ": ", length(ops.traits), " trait", length(ops.traits) == 1 ? "" : "s", ")")
end

# a trait as its declaration's head writes it, with the subject's values: `Indexable{T}, T = Float64`
function _trait_head(g::TraitOperations)
    _is_all(g.trait) && return "methods at " * _shown(g.trait)
    c = contract(g.trait)
    c === nothing && return _shown(g.instance)
    s = isempty(c.params) ? string(nameof(g.trait)) : string(nameof(g.trait), "{", join(c.params, ", "), "}")
    u = Base.unwrap_unionall(g.instance)
    if !isempty(c.params) && u isa DataType && u.name === Base.unwrap_unionall(g.trait).name && !Base.has_free_typevars(u)
        s *= ", " * join((string(p, " = ", _shown(v)) for (p, v) in zip(c.params, u.parameters)), ", ")
    end
    isempty(c.supers) || (s *= " <: " * join((string(x) for x in c.supers), ", "))
    isempty(g.via) || (s *= ", " * g.via)
    return s
end

function _print_lines(io::IO, lines::Vector{OperationLine}, indent::String, width::Int)
    for l in lines
        comment = join(filter(!isempty, [l.note, l.doc]), "; ")
        print(io, "\n", indent, l.text)
        isempty(comment) || print(io, " "^max(1, width - textwidth(l.text) + 1), "# ", comment)
    end
end

function Base.show(io::IO, ::MIME"text/plain", ops::Operations)
    names = String[]
    for g in ops.traits
        _is_all(g.trait) || push!(names, _shown(g.instance))
    end
    if ops.istrait || ops.kind === :boxtype
        print(io, ops.subject, ": ", ops.note)
    else
        T = _type_label(ops.type)
        what = ops.kind in (:box, :wrapper) ? string(isempty(ops.subject) ? "the kept form" : ops.subject, " holds ", _article(T), T) :
               ops.subject == T ? ops.subject :
               isempty(ops.subject) ? uppercasefirst(string(_article(T), T)) : string(ops.subject, " is ", _article(T), T)
        print(io, what, isempty(names) ? ", a member of no trait" : ", a member of " * join(names, ", "))
        isempty(ops.note) || print(io, "\n", ops.note)
    end
    for g in ops.traits
        width = 0
        for l in Iterators.flatten((g.operations, g.fields))          # the comments' column: the contract's lines
            width = max(width, min(textwidth(l.text), 44))
        end
        print(io, "\n\n")
        printstyled(io, _trait_head(g); bold = true)
        g.reached || print(io, " (through unwrap(x))")
        isempty(g.doc) || print(io, "\n  # ", g.doc)
        if !isempty(g.operations)
            print(io, "\n  operations:")
            _print_lines(io, g.operations, "    ", width)
        end
        if !isempty(g.fields)
            print(io, "\n  fields:")
            _print_lines(io, g.fields, "    ", width)
        end
        if !isempty(g.methods)
            _is_all(g.trait) || print(io, "\n  methods at ", nameof(g.trait), ":")
            _print_lines(io, g.methods, "    ", width)
        end
    end
    if !isempty(ops.members)
        print(io, "\n\n")
        printstyled(io, "members"; bold = true)
        for m in ops.members
            print(io, "\n    ", m)
        end
    end
    if !isempty(ops.other) || ops.more > 0
        print(io, "\n\n")
        printstyled(io, "other: methods at ", _type_label(ops.type); bold = true)
        ops.kind in (:box, :wrapper) && print(io, " (through unwrap(x))")
        _print_lines(io, ops.other, "    ", 0)
        ops.more > 0 && print(io, "\n    … and ", ops.more, " more (operations(x; limit = ", length(ops.other) + ops.more, "))")
    end
end

# --- the REPL ---------------------------------------------------------------------------------------------------

"""
    TraitWorld.install_operations_key!(repl = Base.active_repl; key = "\\eo")

Bind Alt-o (`"\\eo"`) at the REPL's Julia prompt to [`operations`](@ref) of the name under the cursor, printed below the
prompt; the line being edited stays. A name is a variable, or a dotted path (`Geometry.Shape`, `x.field`), evaluated
in the REPL's active module. In `startup.jl`:

    atreplinit(repl -> (@eval using TraitWorld; TraitWorld.install_operations_key!(repl)))

or, in a running session, `TraitWorld.install_operations_key!()`.
"""
function install_operations_key!(repl = isdefined(Base, :active_repl) ? Base.active_repl : nothing; key::String = "\eo")
    repl === nothing && throw(ArgumentError("no REPL is running: call it from `atreplinit` in startup.jl, or at the prompt"))
    REPL = Base.REPL_MODULE_REF[]
    REPL === Base && throw(ArgumentError("the REPL is not loaded"))
    LineEdit = REPL.LineEdit
    keymap = Dict{Any,Any}(key => (s, o...) -> _operations_key(s, REPL))
    if !isdefined(repl, :interface)
        # before the REPL starts (`atreplinit`): its interface, made with the key, as Julia's manual shows
        repl.interface = REPL.setup_interface(repl; extra_repl_keymap = keymap)
    else
        mode = repl.interface.modes[1]
        mode.keymap_dict = LineEdit.keymap_merge(mode.keymap_dict, keymap)
    end
    return nothing
end

# the key's action: `operations` of the word under the cursor, printed below the line, which is then redrawn
function _operations_key(s, REPL)
    LineEdit = REPL.LineEdit
    word = LineEdit.current_word_with_dots(s)
    mod = try REPL.active_module() catch; Main end
    term = LineEdit.terminal(s)
    text = try
        ops = _operations_word(mod, word)
        sprint(io -> show(IOContext(io, :color => (try REPL.Terminals.hascolor(term) catch; false end)), MIME("text/plain"), ops))
    catch err
        string("operations: ", sprint(showerror, err))
    end
    try LineEdit.cmove_down(term, LineEdit.input_string_newlines_aftercursor(s)) catch end
    print(term, "\n", text, "\n\n")
    LineEdit.refresh_line(s)
    return nothing
end

"""
    TraitWorld._operations_word(mod, word)

`operations` of `word`, a name or a dotted path of names (`Geometry.Shape`, `x.field`), evaluated in `mod`, and named
by it; an `ArgumentError` for anything else, so that a key press calls nothing but a property's read.
"""
function _operations_word(mod::Module, word::AbstractString)
    w = strip(word)
    isempty(w) && throw(ArgumentError("no name under the cursor"))
    ex = try Meta.parse(w; raise = false) catch; nothing end
    _is_path(ex) || throw(ArgumentError("`$w` is not a name"))
    x = try
        Core.eval(mod, ex)
    catch err
        err isa UndefVarError && throw(ArgumentError("`$w` is not defined in $mod"))
        rethrow()
    end
    return _runtime_site(_operations, x, 12, String(w))::Operations
end
_is_path(@nospecialize(ex)) = ex isa Symbol ||
    (Meta.isexpr(ex, :., 2) && ex.args[2] isa QuoteNode && ex.args[2].value isa Symbol && _is_path(ex.args[1]))
