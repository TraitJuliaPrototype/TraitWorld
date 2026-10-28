# ---------------------------------------------------------------------------
# The machinery's own costs, recorded while a switch is on (W-85): what TraitWorld's checks and folds cost
# during loads (`using`) and at first uses. `JULIA_TW_LOADREPORT=1` switches it on when TraitWorld loads,
# `loadreport_switch!(true)` later; `loadreport()` prints what was recorded (diagnostics.jl). Off, each
# recorded step costs one load of a flag and a branch.
# ---------------------------------------------------------------------------

"Whether the machinery's costs are recorded (`JULIA_TW_LOADREPORT=1`, or `loadreport_switch!`)."
const _LR_ON = Ref(false)
"Per step: the number of times it ran, its time and the compile time in it (ns, Julia's counter)."
const _LR_PARTS = Dict{Tuple{Symbol,Symbol},Vector{UInt64}}()
"Per step and item (a member, a package, a signature): the time and the compile time in it (ns), in the order they ran."
const _LR_ITEMS = Tuple{Symbol,Symbol,Any,UInt64,UInt64}[]
"When the recording started (`time_ns`), and Julia's compile-time counter then."
const _LR_T0 = Ref{UInt64}(0)
const _LR_CT0 = Ref{UInt64}(0)
"A spin lock: steps run in inference too (a member's fold), which must not yield."
const _LR_LOCK = Threads.SpinLock()
"Set while a fold kept in an image is checked at its load (`_member_fold_at_load`)."
const _LR_ATLOAD = Ref(false)

"The clock and Julia's compile-time counter now (ns): where a recorded step starts."
@inline _lr_now() = (time_ns(), Base.cumulative_compile_time_ns()[1])
"Record that step `(group, part)` ran for `item` since `t0` (from `_lr_now`)."
@noinline _lr_done!(group::Symbol, part::Symbol, t0::Tuple{UInt64,UInt64}, @nospecialize(item)) =
    _lr_add!(group, part, time_ns() - t0[1], Base.cumulative_compile_time_ns()[1] - t0[2], item)
"Record that step `(group, part)` ran for `item` and took `ns` nanoseconds, `cns` of them compiling."
@noinline function _lr_add!(group::Symbol, part::Symbol, ns::UInt64, cns::UInt64, @nospecialize(item))
    lock(_LR_LOCK)
    try
        v = get!(() -> UInt64[0, 0, 0], _LR_PARTS, (group, part))
        v[1] += 1
        v[2] += ns
        v[3] += cns
        item === nothing || push!(_LR_ITEMS, (group, part, item, ns, cns))
    finally
        unlock(_LR_LOCK)
    end
    return nothing
end

"""
    @_lr group part item expr

`expr`, its time recorded as step `(group, part)` for `item` where the report is on (`_LR_ON`). `group` may be
an expression (evaluated only when on).
"""
macro _lr(group, part, item, ex)
    return quote
        if _LR_ON[]
            local t0 = _lr_now()
            try
                $(esc(ex))
            finally
                _lr_done!($(esc(group)), $(esc(part)), t0, $(esc(item)))
            end
        else
            $(esc(ex))
        end
    end
end

"The group of a family member's fix: at a package's load (a fold kept in its image), in inference (a fold), or at first use."
_lr_member_group() = _LR_ATLOAD[] ? :member_at_load : _IN_FOLD[] ? :member_in_fold : :member_at_first_use

"""
    loadreport_switch!(on::Bool = true; reset = true)

Switch the recording of the machinery's costs on or off (`JULIA_TW_LOADREPORT=1` switches it on when
TraitWorld loads, so that the loads after it are recorded). With `reset`, what was recorded is dropped and
the clock and Julia's compile-time counter start again.
"""
function loadreport_switch!(on::Bool = true; reset::Bool = true)
    if reset
        lock(_LR_LOCK)
        try
            empty!(_LR_PARTS); empty!(_LR_ITEMS)
        finally
            unlock(_LR_LOCK)
        end
        _LR_T0[] = time_ns()
        on && Base.cumulative_compile_timing(true)
        _LR_CT0[] = Base.cumulative_compile_time_ns()[1]
    end
    _LR_ON[] = on
    return on
end
