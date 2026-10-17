# ---------------------------------------------------------------------------
# Core types: traits, trait objects, witnesses, operation calls.
#
# Inside library code a trait object is a `TObj`, a tuple of views, one per
# trait it carries (with supertraits). Each trait defines one method per
# operation on `TObj{T} where {T >: Trait}`, which forwards to the view's
# implementation. Nothing else has methods for `TObj`, so library code can do
# with a trait object exactly what its traits declare: the contract is
# enforced by dispatch, and `check_worker` reports violations by name.
# ---------------------------------------------------------------------------

"Supertype of every trait: `@trait ColTable{R}` defines `abstract type ColTable{R} <: Trait end`."
abstract type Trait end
# defined before the generators that use it (`_carries_static`): a generator run as plain code
# executes in the world of its definition
"`is_trait(X)`: whether `X` was declared with `@trait`."
is_trait(@nospecialize(X)) = X isa Type && X !== Union{} && X <: Trait

"""
    Callable{A, S, M}

The built-in trait for a function argument: called with arguments of the tuple
type `A`, it returns an `S`. Any callable conforms; every call is checked. `M`
is the mode the library sets as its default: `DynamicCall` (a pointer to the
function's code, the worker compiled once per signature) or `CompiledCall`
(a worker compiled per function type, outside the library's cache). A bound
without `M` accepts either and supplies `DynamicCall`; the caller overrides per
value with `compiled_call(f)` or `dynamic_call(f)`.
"""
abstract type CallMode end
struct DynamicCall <: CallMode end
struct CompiledCall <: CallMode end
abstract type Callable{A<:Tuple,S,M<:CallMode} end

"""
    compiled_call(f), dynamic_call(f), Callable{A, S, M}(f)

The caller's choice of mode for one value, which wins over the bound's default;
the entry strips the wrapper. The long form also fixes the signature, as
FunctionWrappers does.
"""
struct CallAs{M<:CallMode,A,S,F}
    f::F
end
compiled_call(f::F) where {F} = CallAs{CompiledCall,Nothing,Nothing,F}(f)
dynamic_call(f::F) where {F} = CallAs{DynamicCall,Nothing,Nothing,F}(f)
(::Type{Callable{A,S,M}})(f::F) where {A,S,M<:CallMode,F} = CallAs{M,A,S,F}(f)

"One trait's view of a value: the witness that says where its operations come from, and the key `K`."
abstract type AbstractView{X,W,K} end

"""
Where a part of the user's object lives: its byte offset and its field index. The
offset -1 means the object itself (a type that implements the operations).
"""
struct Slot
    off::Int
    idx::Int
end
const SELF = Slot(-1, 0)

"""
    Key{I, F}

The key of a trait that declares fields (note "Terms": what a bound can see): the
implementing type `I` (`Nothing` for a trait with fields only) and `F`, a named-tuple
type of the declared fields' types in the conforming type. A trait without fields is
keyed by its implementing type alone.
"""
struct Key{I,F} end
"The implementing type of a key."
_impl(::Type{K}) where {K} = K
_impl(::Type{Key{I,F}}) where {I,F} = I
"The type of declared field `f` in a key."
_keyfield(::Type{Key{I,F}}, f::Symbol) where {I,F} = fieldtype(F, f)

"""
A view: the witness, the user's object `o` when its type is mutable (`nothing` otherwise),
the slots of the implementing value and of the declared fields, and `parts`, those values
held, typed by the key (note "Declaring a trait": a mutable object is read through, an
immutable one held, which is equivalent because none of its fields can be rebound). Its
type depends on the trait and the key, never on the user's type, so one worker compiled
per key serves every conforming type, mutable or immutable, and an immutable user type is
never boxed.
"""
struct View{X,W,K,N,P} <: AbstractView{X,W,K}
    w::W
    o::Any
    r::Slot
    fs::NTuple{N,Slot}
    parts::P
end
"A view of a value that is its own implementing value, with no declared fields: generic implementations' constraints, `Like` results."
View{X}(w::W, r) where {X,W} = View{X,W,typeof(r),0,Tuple{typeof(r)}}(w, ismutable(r) ? r : nothing, SELF, (), (r,))

"The implementing value a view stands for: the user's object, or its forwarding field, read now (held for an immutable type)."
@inline function _rep(v::View{X,W,K}) where {X,W,K}
    o = getfield(v, :o)
    o === nothing && return getfield(getfield(v, :parts), 1)
    return _loadpart(_impl(K), o, getfield(v, :r))
end
"The key of a view type."
_reptype(::Type{<:AbstractView{X,W,K}}) where {X,W,K} = K

# --- reading and writing the user's object at an offset (experiments/lens/layout.md) ---------------
#
# The loads and stores carry Julia's own alias metadata (TBAA `jtbaa_mutab`), so a loop
# that reads `t.data[i]` while storing into another array vectorizes as in plain Julia;
# without it, LLVM reloads the field after every store (5× on such loops).

@inline _objptr(o) = ccall(:jl_value_ptr, Ptr{Cvoid}, (Any,), o)
const _TBAA_MD = """
!0 = !{!"jtbaa"}
!1 = !{!"jtbaa", !0, i64 0}
!2 = !{!"jtbaa_value", !1, i64 0}
!3 = !{!"jtbaa_mutab", !2, i64 0}
!4 = !{!3, !3, i64 0}
"""
const _LLVM_PRIM = IdDict{Any,String}(Float64 => "double", Float32 => "float", Int64 => "i64", UInt64 => "i64",
                                      Int32 => "i32", UInt32 => "i32", Int16 => "i16", UInt16 => "i16")
@generated function _tbaa_load(p::Ptr{T}) where {T}
    t = T <: Ptr ? "ptr" : get(_LLVM_PRIM, T, nothing)
    t === nothing && return :(unsafe_load(p))
    ir = "define $t @entry(ptr %p) #0 {\n  %v = load $t, ptr %p, align $(Base.datatype_alignment(T)), !tbaa !4\n  ret $t %v\n}\nattributes #0 = { alwaysinline }\n" * _TBAA_MD
    return :(Base.llvmcall(($ir, "entry"), $T, Tuple{Ptr{$T}}, p))
end
@generated function _tbaa_store(p::Ptr{T}, x::T) where {T}
    t = get(_LLVM_PRIM, T, nothing)
    t === nothing && return :(unsafe_store!(p, x); nothing)
    ir = "define void @entry(ptr %p, $t %x) #0 {\n  store $t %x, ptr %p, align $(Base.datatype_alignment(T)), !tbaa !4\n  ret void\n}\nattributes #0 = { alwaysinline }\n" * _TBAA_MD
    return :(Base.llvmcall(($ir, "entry"), Cvoid, Tuple{Ptr{$T},$T}, p, x); nothing)
end

"How a field of declared type `T` is stored: `:singleton`, `:bits` (inline, isbits), `:ref` (a pointer), or `:other` (read with `getfield`)."
function _storage(@nospecialize(T))
    T isa DataType && Base.issingletontype(T) && return :singleton
    isbitstype(T) && return :bits
    (T isa Union && Base.isbitsunion(T)) && return :other
    T isa DataType && Base.allocatedinline(T) && return :other
    return :ref
end
"A part of the user's object, of exactly the type `T` in the key: the object itself, or its field at slot `s`."
@inline function _loadpart(::Type{T}, o, s::Slot) where {T}
    getfield(s, :off) < 0 && return o::T
    return _loadfield(T, o, s)
end
"No implementing type (every operation served by a default): there is no implementing value."
@inline _loadpart(::Type{Nothing}, o, s::Slot) = nothing
"Whether the runtime has the field-offset intrinsics (patched Julia, julia-support.md piece 3)."
const _HAS_FIELD_INTRINSICS = isdefined(Core.Intrinsics, :getfield_at_offset)

@generated function _loadfield(::Type{T}, o, s::Slot) where {T}
    k = _storage(T)
    k === :singleton && return :($(T.instance))
    # the runtime's intrinsic: a load at the offset with Julia's alias metadata, and the null check
    _HAS_FIELD_INTRINSICS && k in (:bits, :ref) &&
        return :(Core.Intrinsics.getfield_at_offset(o, $T, getfield(s, :off))::$T)
    # no GC.@preserve: the trait object holding `o` is live for the call, and no safepoint lies
    # between computing the address and the load (a preserve region boxes values in loops)
    k === :bits && return :(_tbaa_load(Ptr{$T}(_objptr(o) + getfield(s, :off))))
    k === :other && return :(getfield(o, getfield(s, :idx))::$T)
    return quote
        p = _tbaa_load(Ptr{Ptr{Cvoid}}(_objptr(o) + getfield(s, :off)))
        p == C_NULL && throw(UndefRefError())
        unsafe_pointer_to_objref(p)::$T
    end
end
"Write a field of the user's (mutable) object: an isbits field at its offset, any other through `setfield!` and its write barrier."
@generated function _storefield(::Type{T}, o, s::Slot, x) where {T}
    _HAS_FIELD_INTRINSICS && _storage(T) in (:bits, :ref) &&
        return :(Core.Intrinsics.setfield_at_offset(o, $T, getfield(s, :off), x::$T); nothing)
    _storage(T) === :bits && return :(_tbaa_store(Ptr{$T}(_objptr(o) + getfield(s, :off)), x::$T); nothing)
    return :(setfield!(o, getfield(s, :idx), x::$T); nothing)
end

"""
    TObj{T, V}

A trait object inside library code. `T` is the union of the traits it
carries, `V` the tuple of their views. Workers specialize on `V`, so code is
compiled per representation, never per user type.
"""
struct TObj{T,V<:Tuple}
    views::V
    TObj{T,V}(views::V) where {T,V<:Tuple} = new{T,V}(views)
end
"The trait family of a trait instance (`ArrayLike{Float64, 1, Vector{Float64}}` gives `ArrayLike`), or `X` itself."
_family(@nospecialize(X)) = (u = Base.unwrap_unionall(X); u isa DataType && u <: Trait ? u.name.wrapper : X)
"""
    PTag{F, i, v}

In a trait object's trait set: parameter `i` of trait family `F` has the value `v`. The set is a
union of trait families and these tags, never of trait instances with type variables, so a
worker's signature, `TObj{T} where T >: Union{StateVector, PTag{StateVector, 1, Float64}}`,
has no static parameter that its argument does not determine. (With one, `T >: StateVector{Float64, R}`,
Julia cannot specialize the call and passes the trait object boxed.)
"""
struct PTag{F,i,v} end
_isptag(@nospecialize(X)) = X isa DataType && X <: PTag

"The trait set of trait instances: their families, and a tag per parameter they fix (the implementing type excluded)."
function _encode_traits(insts)
    ms = Any[]
    for X in insts
        F = _family(X)
        any(m -> m === F, ms) || push!(ms, F)
        u = Base.unwrap_unionall(X)
        u isa DataType || continue
        ps = u.parameters
        for i in 1:length(ps)-1
            p = ps[i]
            p isa TypeVar && continue
            t = PTag{F,i,p}
            any(m -> m === t, ms) || push!(ms, t)
        end
    end
    return Union{ms...}
end

"""
A trait set or a worker's lower bound decoded into trait patterns: each family applied to the
parameters its tags fix and a type variable for each other one, the implementing type last
(`StateVector{Float64, R} where R`). What the machinery reasons about.
"""
function _decode_traits(@nospecialize(lb))
    ms = Base.uniontypes(lb)
    pats = Any[]
    for F in ms
        (_isptag(F) || !is_trait(F)) && continue
        u = Base.unwrap_unionall(F)
        np = length(u.parameters)
        args = Any[]
        vars = TypeVar[]
        for i in 1:np
            v = nothing
            if i < np
                for m in ms
                    if _isptag(m) && m.parameters[1] === F && m.parameters[2] == i && !(m.parameters[3] isa TypeVar)
                        v = m.parameters[3]
                        break
                    end
                end
            end
            if v === nothing
                tv = TypeVar(i == np ? :Self : Symbol(:P, i))
                push!(vars, tv)
                push!(args, tv)
            else
                push!(args, v)
            end
        end
        body = Core.apply_type(F, args...)
        for tv in reverse(vars)
            body = UnionAll(tv, body)
        end
        push!(pats, body)
    end
    return Union{pats...}
end

@generated function _traitset(::Type{V}) where {V<:Tuple}
    return _encode_traits(Any[p.parameters[1] for p in V.parameters])
end
@inline TObj(views::Tuple) = TObj{_traitset(typeof(views)),typeof(views)}(views)

@inline viewof(t::TObj, ::Type{X}) where {X} = _viewof(X, getfield(t, :views)...)
# a view carries a trait instance (`ArrayLike{Float64, 1, Vector{Float64}}`); `X` is the trait family
@inline _viewof(::Type{X}, v::AbstractView{Y}, rest::AbstractView...) where {X,Y} = Y <: X ? v : _viewof(X, rest...)

# --- trait parameters: associated types (note "Declaring a trait": Parameters) ------------

Base.Experimental.@max_methods 1 function trait_params end
"`trait_params(X)`: the names of trait `X`'s parameters besides the representation, in order."
trait_params(@nospecialize(X)) = ()
Base.Experimental.@max_methods 1 function param end
"""
`param(X, Val(p), R)`: parameter `p` of trait `X` at representation `R`, an
associated type: one value per conformance, defined by the trait's equation
(`T = eltype(R)`) or by the conformance (`@implement ArrayLike{Float64, 1} MyVector`).
"""
param
Base.Experimental.@max_methods 1 function param_bound end
@doc "`param_bound(X, Val(p))`: the bound a trait declares on its parameter `p` (`T <: NumberLike`)." param_bound
"The trait instance a view of representation `R` carries: `X` with its parameters at `R`, the representation last."
function _instance(@nospecialize(X), @nospecialize(R))
    ps = trait_params(X)
    isempty(ps) && return X{R}
    return Core.apply_type(X, Any[param(X, Val(p), R) for p in ps]..., R)
end
"Whether a trait object carrying the trait set `T` carries `X`, a family or a partly applied instance."
_carries(@nospecialize(T), @nospecialize(X)) = any(Y -> Y <: X, Base.uniontypes(_decode_traits(T)))
"""
`_carries` at types known to the compiler, as a constant: a pure computation on types (no method
table read), made by a generator, so compiled code holds its answer and no edge to the reflective
code that computes it (whose native code a load may invalidate).
"""
@generated _carries_static(::Type{T}, ::Type{X}) where {T,X} = _carries(T, X)

# --- dynamic values ----------------------------------------------------------

# --- witness tables: a dynamic value's operations as pointers ------------------

"""
A dynamic value's witness table: for each operation of its trait (in declaration order), a pointer
to code compiled for the operation at the value's trait-object type, with the declared argument
and result types (Swift's witness tables; `Erased`'s technique). Filled on an operation's first
call for that type, shared by all dynamic values of the pair. The pointers are this process's:
`session` keeps a table stored in an image (a dynamic value made at precompile time) from being
used in another process; such a value takes the dispatching path.
"""
struct _Witness
    session::UInt
    ptrs::Memory{Ptr{Cvoid}}
end
"This process's token for witness tables (set when TraitWorld is initialized)."
const _WIT_SESSION = Ref{UInt}(0)
"Whether dynamic values call through witness tables (`JULIA_TW_WITNESS=0`: always the dispatching path, for comparison)."
const _WIT_ON = Ref(true)
const _WIT_TABLES = IdDict{Any,_Witness}()
"An operation's declarations for witness tables: `(f, argument types, result type)` per declaration, or `nothing` where the dispatching path stays (constructor operations); `@trait` defines it."
_wit_decls(@nospecialize(F)) = ()
"The witness table of trait `X` for trait objects of type `typeof(t)` (empty pointers, filled on first calls)."
@noinline function _wit_table(@nospecialize(X), @nospecialize(t))
    key = (X, typeof(t))
    w = @lock _LOCK get(_WIT_TABLES, key, nothing)
    w === nothing || return w
    n = length(_wit_decls(_family(X)))
    ptrs = Memory{Ptr{Cvoid}}(undef, n::Int)
    fill!(ptrs, C_NULL)
    w = _Witness(_WIT_SESSION[], ptrs)
    return @lock _LOCK get!(_WIT_TABLES, key, w)
end
"The callee behind a witness pointer: the operation at the trait object's own type, its result asserted."
struct _WitOp{F,RT} end
# fixed arities: a varargs callee would not be specialized behind the pointer (as `_CallWrap`)
(::_WitOp{F,RT})(o) where {F,RT} = F.instance(o)::RT
(::_WitOp{F,RT})(o, a) where {F,RT} = F.instance(o, a)::RT
(::_WitOp{F,RT})(o, a, b) where {F,RT} = F.instance(o, a, b)::RT
(::_WitOp{F,RT})(o, a, b, c) where {F,RT} = F.instance(o, a, b, c)::RT
(::_WitOp{F,RT})(o, a, b, c, d) where {F,RT} = F.instance(o, a, b, c, d)::RT
(::_WitOp{F,RT})(o, a, b, c, d, e) where {F,RT} = F.instance(o, a, b, c, d, e)::RT
(::_WitOp{F,RT})(o, a, b, c, d, e, g) where {F,RT} = F.instance(o, a, b, c, d, e, g)::RT
_wdecl(@nospecialize(T)) = isconcretetype(T) ? _cdecl(T) : Any        # callee side
_wctype(@nospecialize(T)) = isconcretetype(T) ? _ctype(T) : Any       # caller side
_wret(@nospecialize(T)) = isconcretetype(T) ? _ctype(T) : Any
@generated function _wptr(::Type{W}, ::Type{TO}, ::Type{AT}) where {W,TO,AT}
    RT = W.parameters[2]
    return :(@cfunction($(W()), $(_wret(RT)), (Ref{$TO}, $(map(_wdecl, AT.parameters)...))))
end
"Fill pointer `k` of witness table `w` for trait object `t` (the first call of that operation for its type)."
@noinline function _wit_fill!(w::_Witness, k::Int, @nospecialize(f), @nospecialize(AT), @nospecialize(RT), @nospecialize(t))
    p = try
        _wptr(_WitOp{typeof(f), RT}, typeof(t), AT)
    catch
        C_NULL
    end
    p = p isa Ptr{Cvoid} ? p : C_NULL
    @inbounds w.ptrs[k] = p
    return p::Ptr{Cvoid}
end
"""
    Dynamic{X}

A value of any type conforming to trait `X`, kept beyond a call and reached
through `X`'s operations (note "Dynamic values"). It keeps a trait object of
`X`: made from one inside a trait module, `Dynamic{X}(t)`, or by storing one
where a `Dynamic{X}` is declared, so its type decides it. An operation of `X`
on it dispatches on the trait object inside and asserts the declared result
type; passed to a function bounded by `X`, it is opened, and the worker for
its representation runs.
"""
struct Dynamic{X}
    t::Any
    w::_Witness          # X's operations compiled for the trait object's type: one indirect call each
    function Dynamic{X}(t::TObj{T}) where {X,T}
        _carries_static(T, X) || Base.inferencebarrier(_dyn_refuse)(X, T)
        tn = _narrow(X, t)               # the trait object is the user's object: a kept value follows its fields
        return new{X}(tn, _wit_table(X, tn))
    end
end
"""
A dynamic value of `X` keeps only the views of `X` and its supertraits: what its operations and
the bounds that open it can see (note "Keys"). A column made from a reader's `CSVColumn` trait
object and kept as a `Dynamic{Column}` then runs the table's workers compiled for `Column` alone,
not new ones for the pair of views. A trait object with one view is kept as it is.
"""
@inline _narrow(::Type{X}, t::TObj{T,V}) where {X,T,V} = fieldcount(V) == 1 ? t : Base.inferencebarrier(_narrow_slow)(X, t)
const _NARROW = IdDict{Any,Any}()
function _narrow_slow(@nospecialize(X), @nospecialize(t::TObj))
    V = typeof(getfield(t, :views))
    keep = @lock _LOCK get(_NARROW, (X, V), nothing)
    if keep === nothing
        F = _family(X)
        if F isa DataType || F isa UnionAll
            fams = Any[]
            for B in bound_traits(F), Y in trait_closure(_family(B))
                push!(fams, _family(Y))
            end
            keep = Tuple(i for (i, P) in enumerate(V.parameters) if any(G -> P.parameters[1] <: G, fams))
        else
            keep = Tuple(1:fieldcount(V))
        end
        @lock _LOCK (_NARROW[(X, V)] = keep)
    end
    length(keep) == fieldcount(V) && return t
    views = getfield(t, :views)
    return TObj(Tuple(views[i] for i in keep))
end
Dynamic{X}(d::Dynamic{X}) where {X} = d
Base.convert(::Type{Dynamic{X}}, t::TObj) where {X} = Dynamic{X}(t)
@noinline _dyn_refuse(@nospecialize(X), @nospecialize(T)) =
    throw(ArgumentError("a trait object carrying $(join(string.(Base.uniontypes(_decode_traits(T))), ", ")) cannot be kept as a Dynamic{$X}"))
"The trait object a dynamic value keeps: what a bound opens."
@inline opened(d::Dynamic) = getfield(d, :t)

"""
Operation `k` of a dynamic value's trait, declared with argument types `AT` and result type `RT`:
one indirect call through the witness table, typed by the declaration; the dispatching path for
arguments outside the declaration, for a table of another process, and where no pointer can be made.
"""
@generated function _dyn_call(dyn::Dynamic, ::Val{k}, f::F, ::Type{AT}, ::Type{RT}, args::Vararg{Any,N}) where {k,F,AT,RT,N}
    slow = :(_dyn_assert(f(opened(dyn), args...), RT))
    # a trimmed build makes no pointers at run time: it dispatches, to the targets verify_main enumerates
    (length(AT.parameters) == N <= 6 && !_closed_build()) || return slow
    cts = map(_wctype, AT.parameters)
    argex = [:(args[$i]) for i in 1:N]
    return quote
        Base.@_inline_meta
        w = getfield(dyn, :w)
        if args isa AT && w.session === _WIT_SESSION[] && _WIT_ON[] && $k <= length(w.ptrs)
            p = @inbounds w.ptrs[$k]
            p == C_NULL && (p = _wit_fill!(w, $k, f, AT, RT, getfield(dyn, :t)))
            if p != C_NULL
                x = ccall(p, $(_wret(RT)), (Any, $(cts...)), getfield(dyn, :t), $(argex...))
                return x::RT
            end
        end
        return $slow
    end
end

# equal when they keep the same trait object: same representation type, same implementation, egal data
Base.:(==)(a::Dynamic{X}, b::Dynamic{X}) where {X} = getfield(a, :t) === getfield(b, :t)
Base.hash(d::Dynamic, h::UInt) = hash(getfield(d, :t), hash(:TraitWorldDynamic, h))
Base.show(io::IO, d::Dynamic{X}) where {X} = print(io, "Dynamic{", X, "} at ", _represented(typeof(getfield(d, :t))))
_represented(@nospecialize(T)) = T <: TObj ? join(unique([sprint(_show_key, v.parameters[3]) for v in T.parameters[2].parameters]), ", ") : string(T)
@inline _dyn_assert(x, ::Type{S}) where {S} = x::S

# --- printing by bound and representation (note "Identical or error", findings §16, §17) --------
#
# A trait object's type is machinery: `TObj{ColTable{Ramp}, Tuple{View{ColTable{Ramp}, Impl{()}, Ramp}}}`.
# It prints as what a reader needs, the bound and the representation, `ColTable at Ramp`, in
# stack traces, `MethodError`s and `typeof` alike. The concrete type stays the worker's key.

"Whether `T` is a trait object's concrete type, with views whose parameters are all known."
_printable_tobj(@nospecialize(T)) = T isa DataType && T <: TObj && T.parameters[2] isa DataType &&
    all(v -> v isa DataType && v <: AbstractView && v.parameters[1] isa DataType, T.parameters[2].parameters)

"A trait instance without its representation: `StateVector{Float64}` for `StateVector{Float64, Vector{Float64}}`."
function _show_bound(io::IO, @nospecialize(X))
    show(io, Base.typename(X).wrapper)
    ps = X.parameters[1:end-1]
    isempty(ps) && return
    print(io, "{")
    for (i, p) in enumerate(ps)
        i > 1 && print(io, ", ")
        show(io, p)
    end
    print(io, "}")
end

function _show_tobj(io::IO, @nospecialize(T))
    # views grouped by representation and how it is held: `ColTable & RowTable at Vector{Vector{Float64}}`
    groups = Any[]
    for V in T.parameters[2].parameters
        X, W, R = V.parameters[1], V.parameters[2], V.parameters[3]
        how = W <: Dyn ? " (dynamic)" : ""
        k = findfirst(g -> g[1] === R && g[2] == how, groups)
        k === nothing ? push!(groups, (R, how, Any[X])) : push!(groups[k][3], X)
    end
    for (i, (R, how, Xs)) in enumerate(groups)
        i > 1 && print(io, ", ")
        for (j, X) in enumerate(Xs)
            j > 1 && print(io, " & ")
            _show_bound(io, X)
        end
        print(io, " at ")
        _show_key(io, R)
        print(io, how)
    end
end

# A trait object's type prints by bound and key, wherever Julia prints a type, through type
# printers (`Base.Experimental.register_type_printer`, patched Julia) rather than methods of
# `show(::IO, ::Type{<:TObj})`: such a method invalidates every caller compiled for
# `show(::IO, ::Type)`, most code that prints a type (CSV's parser among them: 1.0 s on its
# first read, session 26). Without the registry (stock Julia) types print as Julia prints them.
function _show_tobj_type(io::IO, @nospecialize(T))
    _printable_tobj(T) || return _show_type_plain(io, T)
    return _show_tobj(io, T)
end
_show_type_plain(io::IO, @nospecialize(T)) =
    isdefined(Base.Experimental, :show_type_plain) ? Base.Experimental.show_type_plain(io, T) : invoke(show, Tuple{IO,Type}, io, T)
"Register the printers of trait objects' and function bounds' types, where Julia has the registry."
function _register_type_printers()
    isdefined(Base.Experimental, :register_type_printer) || return nothing
    Base.Experimental.register_type_printer(Base.typename(TObj), _show_tobj_type)
    Base.Experimental.register_type_printer(Base.typename(CObj), _show_cobj_type)
    return nothing
end
Base.show(io::IO, t::TObj) = (print(io, "trait object "); _show_tobj(io, typeof(t)))
"A key as a reader wants it: the implementing type, then the declared fields' types, `Vector{Float64}; u::Vector{Float64}, p::Params`."
function _show_key(io::IO, @nospecialize(K))
    if K isa DataType && K <: Key && length(K.parameters) == 2
        I, F = K.parameters
        I === Nothing || (show(io, I); print(io, "; "))
        F isa DataType && F <: NamedTuple || return show(io, F)
        names, types = F.parameters[1], F.parameters[2].parameters
        print(io, join(("$n::$(sprint(show, t))" for (n, t) in zip(names, types)), ", "))
    else
        show(io, K)
    end
end

# --- fields: properties a trait declares --------------------------------------

Base.Experimental.@max_methods 1 function trait_fields end
"`trait_fields(X)`: the fields trait `X` declares, as `(name, writable)` pairs."
trait_fields(@nospecialize(X)) = ()
Base.Experimental.@max_methods 1 function field_type end
@doc "`field_type(X, Val(f), R)`: the declared type of field `f` at representation `R`." field_type
Base.Experimental.@max_methods 1 function trait_uses_self end
"`trait_uses_self(X)`: whether trait `X`'s declarations name the implementing type (`Self` in an operation's types, or a defining equation)."
trait_uses_self(@nospecialize(X)) = false
Base.Experimental.@max_methods 1 function _fieldmatch end
@doc "`_fieldmatch(X, Val(f), FT)`: the parameters field `f` of trait `X` defines, matched against its type `FT` in a conforming type (methods added by @trait)." _fieldmatch
Base.Experimental.@max_methods 1 function trait_field_params end
"`trait_field_params(X)`: the parameters of `X` that its declared fields define (`u::U`, `data::Vector{T}`)."
trait_field_params(@nospecialize(X)) = ()
Base.Experimental.@max_methods 1 function field_isrep end
"`field_isrep(X, Val(f))`: whether field `f` is declared with the implementing type: it names the forwarding field of a one-line conformance."
field_isrep(@nospecialize(X), @nospecialize(f)) = false

# `t.f` on a trait object: a field one of its traits declares (methods added by @trait), else an error
@inline Base.getproperty(t::TObj, s::Symbol) = _tgetprop(t, Val(s))
@inline Base.setproperty!(t::TObj, s::Symbol, x) = _tsetprop!(t, Val(s), x)
@noinline _tgetprop(t::TObj, ::Val{s}) where {s} = Base.inferencebarrier(_nofield)(typeof(t), s)
@noinline _tsetprop!(t::TObj, ::Val{s}, x) where {s} = Base.inferencebarrier(_nofield)(typeof(t), s)
@noinline _nofield(@nospecialize(T), s::Symbol) =
    throw(ArgumentError("`t.$s`: no trait this trait object carries declares a field `$s`"))
@noinline _readonly(@nospecialize(X), s::Symbol) = throw(ArgumentError("field `$s` of $X is `const`: read-only"))
Base.getproperty(d::Dynamic, s::Symbol) = getproperty(getfield(d, :t), s)
Base.setproperty!(d::Dynamic, s::Symbol, x) = setproperty!(getfield(d, :t), s, x)

Base.Experimental.@max_methods 1 function _fieldpos end
@doc "`_fieldpos(X, Val(f))`: the position of declared field `f` among trait `X`'s fields (methods added by @trait)." _fieldpos
"The type of declared field `f` in key `K`: the conforming type's own field type."
_fieldkeytype(::Type{X}, ::Val{f}, ::Type{K}) where {X,f,K} = K <: Key ? _keyfield(K, f) : field_type(X, Val(f), K)

"A field `f` of trait `X` read on a trait object: a load from the user's object."
@inline function fieldget(::Type{X}, ::Val{f}, t::TObj) where {X,f}
    v = viewof(t, X)
    return _fget(X, Val(f), getfield(v, :w), v, _reptype(typeof(v)))
end
@inline function _fget(::Type{X}, ::Val{f}, w, v, ::Type{K}) where {X,f,K}
    o = getfield(v, :o)
    o === nothing && return getfield(getfield(v, :parts), 1 + _fieldpos(X, Val(f)))
    return _loadpart(_fieldkeytype(X, Val(f), K), o, getfield(v, :fs)[_fieldpos(X, Val(f))])
end
"A field `f` of trait `X` written on a trait object: a store into the user's object, as `u.f = x` in plain Julia."
@inline function fieldset!(::Type{X}, ::Val{f}, t::TObj, x) where {X,f}
    v = viewof(t, X)
    K = _reptype(typeof(v))
    T = _fieldkeytype(X, Val(f), K)
    y = x::T
    o = getfield(v, :o)
    o === nothing && Base.inferencebarrier(_readonly)(X, f)     # the conformance check refuses writable fields on immutable types
    _storefield(T, o, getfield(v, :fs)[_fieldpos(X, Val(f))], y)
    return y
end

# --- witnesses -------------------------------------------------------------

"The representation's own methods implement the trait; `D` lists the operations served by the trait's defaults."
struct Impl{D} end
"A constraint trait's witness inside a generic implementation."
struct Wit{X,W}
    w::W
end
Wit{X}(w::W) where {X,W} = Wit{X,W}(w)
"A generic implementation `k` of trait `X`, with the witnesses of its constraint traits; `D` lists the operations left to defaults."
struct Generic{X,k,S<:Tuple,D}
    sub::S
end
"""
A type's own operations (`@implement … dynamic`): erased calls; the trait's
defaults for the operations it leaves out (`D`), which then call its own
operations. Never the representation's implementation: a type that brings its
own behaviour on a shared representation means something else by it.
"""
struct Dyn{NT<:NamedTuple,D}
    table::NT
end

# --- trait declarations, as methods defined by `@trait` --------------------

Base.Experimental.@max_methods 1 function trait_ops end
@doc "`trait_ops(X)`: the operation names of trait `X`, in declaration order." trait_ops
Base.Experimental.@max_methods 1 function op_function end
@doc "`op_function(X, Val(op))`: the function an operation is." op_function
Base.Experimental.@max_methods 1 function op_ret end
@doc "`op_ret(X, Val(op), R, Val(N))`: the declared result type at representation `R`, for `N` arguments after `r`." op_ret
Base.Experimental.@max_methods 1 function op_args end
@doc "`op_args(X, Val(op), R, Val(N))`: the declared types of the arguments after `r`, as a tuple type." op_args
Base.Experimental.@max_methods 1 function op_default end
@doc "`op_default(X, Val(op), t, args...)`: the trait's default for an operation, with `t` a trait object." op_default
Base.Experimental.@max_methods 1 function generic_op end
@doc "`generic_op(X, Val(k), Val(op), t, args...)`: generic implementation `k` of an operation." generic_op
Base.Experimental.@max_methods 1 function generic_rec end
@doc "`generic_rec(X, Val(k))`: the constraints of generic implementation `k` of trait `X` (one method per implementation)." generic_rec
Base.Experimental.@max_methods 1 function has_default end
has_default(@nospecialize(X), @nospecialize(op)) = false
Base.Experimental.@max_methods 1 function is_mutating end
is_mutating(@nospecialize(X), @nospecialize(op)) = false
Base.Experimental.@max_methods 1 function trait_concreteness end
"""
`trait_concreteness(X)`: what trait `X` asks of its keys (decision 1, session 27): `:none` (the
default: a key may be abstract, silently), `:warn` (`@warn_on_abstract` in the trait's body: a
conformance with an abstract key warns) or `:concrete_only` (`@concrete_only`: such a conformance,
or a family member at an abstract parameter, is refused).
"""
trait_concreteness(@nospecialize(X)) = :none
Base.Experimental.@max_methods 1 function supertraits end
"`supertraits(X)`: traits whose operations `X` includes; their views travel with every `X` view."
supertraits(@nospecialize(X)) = ()
Base.Experimental.@max_methods 1 function bundle end
"`bundle(X)`: for a bundle trait, the traits it names; `t::Table` means `t::(ColTable, RowTable)`."
bundle(@nospecialize(X)) = nothing

# --- operation calls -------------------------------------------------------

struct TraitArgumentError <: Exception
    trait::Any
    op::Symbol
    R::Any
    args::Any
end
Base.showerror(io::IO, e::TraitArgumentError) =
    print(io, "TraitArgumentError: operation `", e.op, "` of trait ", e.trait, " at representation ", e.R,
          " is declared for arguments ", op_args(e.trait, Val(e.op), e.R, Val(length(e.args))),
          ", got ", typeof(e.args))

"""
An operation call on a trait object: check the arguments against the
declaration, run the implementation the witness names, assert the result to
the declared type. Everything folds for a known view type.
"""
@inline function opcall(::Type{X}, ::Val{op}, f::F, t::TObj, args::Vararg{Any,N}) where {X,op,F,N}
    v = viewof(t, X)
    K = _reptype(typeof(v))
    args isa op_args(X, Val(op), K, Val(N)) || throw(TraitArgumentError(X, op, K, args))
    x = _dispatch(X, Val(op), f, getfield(v, :w), _rep(v), t, args...)
    return x::op_ret(X, Val(op), K, Val(N))
end

# A default receives the whole trait object, with its supertraits' views, so it
# may call their operations too (`lastel(r) = r[length(r)]` with `length` from HasLength).
@inline function _dispatch(::Type{X}, ::Val{op}, f::F, w::Impl{D}, r, t, args...) where {X,op,F,D}
    Base.sym_in(op, D) && return op_default(X, Val(op), t, args...)
    return f(r, args...)
end
@inline function _dispatch(::Type{X}, ::Val{op}, f::F, w::Generic{X,k,S,D}, r, t, args...) where {X,op,F,k,S,D}
    Base.sym_in(op, D) && return op_default(X, Val(op), t, args...)
    return generic_op(X, Val(k), Val(op), _subobj(w.sub, r), args...)
end
@inline function _dispatch(::Type{X}, ::Val{op}, f::F, w::Dyn{NT,D}, r, t, args...) where {X,op,F,NT,D}
    Base.sym_in(op, fieldnames(NT)) && return getfield(w.table, op)(r, args...)
    return op_default(X, Val(op), t, args...)
end

@inline _subobj(sub::Tuple, r) = TObj(_subviews(r, sub...))
@inline _subviews(r) = ()
@inline _subviews(r, s::Wit{X}, rest...) where {X} = (View{X}(s.w, r), _subviews(r, rest...)...)

# --- Callable: erased function pointers and checked calls ------------------

"""
    Erased{A, S}

A function from above, erased to a pointer to its code compiled for `A`
(the FunctionWrappers.jl technique). Library code compiled for an `Erased{A,
S}` serves every function with that signature; each call is indirect. The
result is asserted, never converted.
"""
struct Erased{A,S}
    ptr::Ptr{Cvoid}
    obj::Any
end
struct _CallWrap{S} end
# fixed arities: a varargs callee would not be specialized behind the pointer
(::_CallWrap{S})(o) where {S} = o()::S
(::_CallWrap{S})(o, a) where {S} = o(a)::S
(::_CallWrap{S})(o, a, b) where {S} = o(a, b)::S
(::_CallWrap{S})(o, a, b, c) where {S} = o(a, b, c)::S
(::_CallWrap{S})(o, a, b, c, d) where {S} = o(a, b, c, d)::S
(::_CallWrap{S})(o, a, b, c, d, e) where {S} = o(a, b, c, d, e)::S
(::_CallWrap{S})(o, a, b, c, d, e, f) where {S} = o(a, b, c, d, e, f)::S
# The callee side declares concrete types (`Ref{T}` for non-bits values), so
# the call inside is static; the caller passes non-bits values as boxes
# (`Any`): the same pointer, without allocating a `RefValue`.
# (a zero-size type, `Nothing`, is no C type: it goes as a reference too)
_ctype(@nospecialize(T)) = isbitstype(T) && sizeof(T) > 0 ? T : Any
_cdecl(@nospecialize(T)) = isbitstype(T) && sizeof(T) > 0 ? T : Ref{T}
@generated function _fptr(::Type{A}, ::Type{S}, ::Type{F}) where {A,S,F}
    ats = map(_cdecl, A.parameters)
    return :(@cfunction($(_CallWrap{S}()), $(_ctype(S)), ($(Ref{F}), $(ats...))))
end
Erased{A,S}(f::F) where {A,S,F} = Erased{A,S}(_fptr(A, S, F), f)
@generated function (e::Erased{A,S})(args...) where {A,S}
    length(A.parameters) <= 6 || return :(error("Erased: at most 6 arguments"))
    ats = map(_ctype, A.parameters)
    argex = [:(args[$i]) for i in 1:length(ats)]
    return quote
        Base.@_inline_meta
        x = ccall(e.ptr, $(_ctype(S)), (Any, $(ats...)), e.obj, $(argex...))
        x::$S
    end
end

"""
    CObj{A, S, F}

A function inside library code, bounded by `Callable{A, S}`: the function
itself (`F` its type: specialized, the call inlined) or an `Erased{A, S}`.
Calling it checks the arguments against `A` and asserts the result to `S`.
"""
struct CObj{A,S,F}
    f::F
end
CObj{A,S}(f::F) where {A,S,F} = CObj{A,S,F}(f)
@inline function (c::CObj{A,S})(args...) where {A,S}
    args isa A || throw(MethodError(c.f, args))
    return c.f(args...)::S
end

# a function inside library code prints as its bound and how it is called (a type printer,
# registered in `__init__`: see `_register_type_printers`)
function _show_cobj_type(io::IO, @nospecialize(T))
    T isa DataType && length(T.parameters) == 3 && T.parameters[3] isa Type ||
        return _show_type_plain(io, T)
    A, S, F = T.parameters
    print(io, "Callable{")
    show(io, A); print(io, ", "); show(io, S)
    print(io, "} at ")
    F <: Erased ? print(io, "DynamicCall") : show(io, F)
end

"""
    CMulti{C}

A function argument bounded by several `Callable`s, one per signature it is
called at: a tuple of `CObj`. A call picks the signature its arguments match.
"""
struct CMulti{C<:Tuple}
    cs::C
end
@generated function (m::CMulti{C})(args...) where {C}
    for (i, c) in enumerate(C.parameters)
        A = c.parameters[1]
        Tuple{args...} <: A && return :(m.cs[$i](args...))
    end
    return :(throw(MethodError(m, args)))
end
