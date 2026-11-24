//// Tables: finite maps from keys to values.
////
//// Lean gives a spec its meaning, so the bodies here only let a spec
//// compile; Gleam never runs them.
////
//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`
//// in lean/. DO NOT EDIT.

import gleam/option.{type Option}
import tazuna/bag.{type Bag}

/// A finite map from keys to values; at most one value per key.
pub type Table(k, v)

/// The table without keys.
pub fn new() -> Table(k, v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// A table of the pairs; a later pair replaces an earlier one's value.
pub fn from_list(_pairs: List(#(k, v))) -> Table(k, v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The table with the key mapped to the value, replacing any value it had.
pub fn insert(_table: Table(k, v), _key: k, _value: v) -> Table(k, v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The table without the key.
pub fn remove(_table: Table(k, v), _key: k) -> Table(k, v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The key's value, if the table has the key.
pub fn get(_table: Table(k, v), _key: k) -> Option(v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The number of keys.
pub fn size(_table: Table(k, v)) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// The keys.
pub fn keys(_table: Table(k, v)) -> Bag(k) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The values, one occurrence per key.
pub fn values(_table: Table(k, v)) -> Bag(v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The entries that satisfy the predicate.
pub fn filter(
  _table: Table(k, v),
  keeping _keeping: fn(k, v) -> Bool,
) -> Table(k, v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// Each value transformed, keys kept.
pub fn map(_table: Table(k, v), with _with: fn(k, v) -> w) -> Table(k, w) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The number of entries that satisfy the predicate.
pub fn count(_table: Table(k, v), where _where: fn(k, v) -> Bool) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// Whether some entry satisfies the predicate.
pub fn any(
  _table: Table(k, v),
  satisfying _satisfying: fn(k, v) -> Bool,
) -> Bool {
  panic as "tazuna's built-ins run only in the engine"
}

/// Whether every entry satisfies the predicate.
pub fn all(
  _table: Table(k, v),
  satisfying _satisfying: fn(k, v) -> Bool,
) -> Bool {
  panic as "tazuna's built-ins run only in the engine"
}

/// `use value <- table.lookup(table, key, or: rejection)`: the rest of the block with the key's value, else the rejection.
pub fn lookup(
  _table: Table(k, v),
  _key: k,
  or _rejection: e,
  then _then: fn(v) -> Result(a, e),
) -> Result(a, e) {
  panic as "tazuna's built-ins run only in the engine"
}
