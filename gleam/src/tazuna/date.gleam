//// Dates: days without a calendar.
////
//// Lean gives a spec its meaning, so the bodies here only let a spec
//// compile; Gleam never runs them.
////
//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`
//// in lean/. DO NOT EDIT.

/// A day. Dates have no calendar: a spec adds days and counts the days between two dates.
pub type Date

/// The date that many days later (earlier when negative).
pub fn add_days(_date: Date, _days: Int) -> Date {
  panic as "tazuna's built-ins run only in the engine"
}

/// The days from the first date to the second: negative when it is earlier.
pub fn days_between(from _from: Date, to _to: Date) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}
