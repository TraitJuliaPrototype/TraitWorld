# The runtime's interface for sets and memberships (compiler §4).

_open_set!(@nospecialize(T)) = ccall(:jl_set_open_set, Cvoid, (Any,), T)
_set_contract!(@nospecialize(T), @nospecialize(c)) = ccall(:jl_set_contract, Cvoid, (Any, Any), T, c)

"Declare `member` a member of `instance` (compiler §4.2). The caller continues with `Expr(:latestworld)`."
function _declare!(@nospecialize(member), @nospecialize(instance), mod::Module,
                   @nospecialize(by), receiver::Symbol)
    return ccall(:jl_declare_membership, Any, (Any, Any, Any, Any, Any),
                 member, instance, mod, by, receiver)
end

"whether `X` is a trait: an open set"
istrait(@nospecialize(X)) = (dt = Base.unwrap_unionall(X); dt isa DataType && ccall(:jl_is_open_set, Cint, (Any,), dt) != 0)
