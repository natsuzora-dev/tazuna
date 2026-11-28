//// Durations: lengths of time, each written with its unit.
////
//// Lean gives a spec its meaning, so the bodies here only let a spec
//// compile; Gleam never runs them.
////
//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`
//// in lean/. DO NOT EDIT.

/// A length of time, to the millisecond. Only `milliseconds`, `seconds`, `minutes` and `hours` make one, so every length a spec writes names its unit.
pub type Duration

/// That many milliseconds.
pub fn milliseconds(_amount: Int) -> Duration {
  panic as "tazuna's built-ins run only in the engine"
}

/// That many seconds.
pub fn seconds(_amount: Int) -> Duration {
  panic as "tazuna's built-ins run only in the engine"
}

/// That many minutes.
pub fn minutes(_amount: Int) -> Duration {
  panic as "tazuna's built-ins run only in the engine"
}

/// That many hours.
pub fn hours(_amount: Int) -> Duration {
  panic as "tazuna's built-ins run only in the engine"
}

/// The duration as a number of milliseconds.
pub fn to_milliseconds(_duration: Duration) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}
