//// Instants: points in time a spec cannot write, only move and compare.
////
//// Lean gives a spec its meaning, so the bodies here only let a spec
//// compile; Gleam never runs them.
////
//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`
//// in lean/. DO NOT EDIT.

/// A point in time, to the millisecond. No spec can write one: it comes from a context's `now`, from an input, or from moving another by a duration, so what a spec means does not change when every instant moves by the same amount.
pub type Instant

/// The instant that many milliseconds later (earlier when negative).
pub fn add(_instant: Instant, _ms: Int) -> Instant {
  panic as "tazuna's built-ins run only in the engine"
}

/// The milliseconds from the first instant to the second: negative when it is earlier.
pub fn diff(from _from: Instant, to _to: Instant) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// Whether the first instant is earlier than the second.
pub fn is_before(_instant: Instant, _other: Instant) -> Bool {
  panic as "tazuna's built-ins run only in the engine"
}

/// Whether the first instant is later than the second.
pub fn is_after(_instant: Instant, _other: Instant) -> Bool {
  panic as "tazuna's built-ins run only in the engine"
}
