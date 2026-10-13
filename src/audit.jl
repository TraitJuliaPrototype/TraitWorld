# ---------------------------------------------------------------------------
# The error split on stock Julia: PiracyError (the audit itself is ported in M6).
# ---------------------------------------------------------------------------

"""
    PiracyError

Raised when trait-bound code would run on top of a method defined by a
package that owns neither the function nor its argument types. `catch`
blocks inside trait modules rethrow it.
"""
struct PiracyError <: Exception
    msg::String
end
Base.showerror(io::IO, e::PiracyError) = print(io, "PiracyError: ", e.msg)
