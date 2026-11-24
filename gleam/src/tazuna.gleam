//// The tazuna DSL. Lean gives a spec its meaning, so the bodies here only
//// let a spec compile; Gleam never runs them.

import gleam/option.{type Option}
import tazuna/internal/launch

/// `gleam run -m tazuna -- <command> <root> [...]` checks the spec whose
/// root module is `src/<root>.gleam`.
pub fn main() -> Nil {
  launch.main()
}

// Built-ins begin. `lake exe gen-dsl --write ..` in lean/ writes them; do not edit.
/// A multiset: two bags are equal when each value occurs as often in both.
pub type Bag(a)

/// A finite map from keys to values; at most one value per key.
pub type Table(k, v)

/// A day. Dates have no calendar: a spec adds days and counts the days between two dates.
pub type Date

/// An identifier a step makes fresh; ids compare with `==` only.
pub type Id

pub type Spec

pub type PickError {
  Empty
  Tie
}

/// A point in time, in milliseconds.
pub type Instant =
  Int

/// A length of time, in milliseconds.
pub type Duration =
  Int

/// The number of code points.
pub fn length(_string: String) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// A bag of the list's items.
pub fn bag_from_list(_items: List(a)) -> Bag(a) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The bag with one more occurrence of the item.
pub fn bag_insert(_bag: Bag(a), _item: a) -> Bag(a) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The number of items, counting each occurrence.
pub fn bag_size(_bag: Bag(a)) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// The items that satisfy the predicate.
pub fn bag_filter(_bag: Bag(a), keeping _keeping: fn(a) -> Bool) -> Bag(a) {
  panic as "tazuna's built-ins run only in the engine"
}

/// Each item transformed, occurrences kept.
pub fn bag_map(_bag: Bag(a), with _with: fn(a) -> b) -> Bag(b) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The number of items that satisfy the predicate.
pub fn bag_count(_bag: Bag(a), where _where: fn(a) -> Bool) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// The sum of the function over the items.
pub fn bag_sum(_bag: Bag(a), of _of: fn(a) -> Int) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// Whether some item satisfies the predicate.
pub fn bag_any(_bag: Bag(a), satisfying _satisfying: fn(a) -> Bool) -> Bool {
  panic as "tazuna's built-ins run only in the engine"
}

/// Whether every item satisfies the predicate.
pub fn bag_all(_bag: Bag(a), satisfying _satisfying: fn(a) -> Bool) -> Bool {
  panic as "tazuna's built-ins run only in the engine"
}

/// Whether the item occurs in the bag.
pub fn bag_contains(_bag: Bag(a), _item: a) -> Bool {
  panic as "tazuna's built-ins run only in the engine"
}

/// The one item with the least key; Empty or Tie when there is not exactly one.
pub fn bag_min_by(_bag: Bag(a), by _by: fn(a) -> Int) -> Result(a, PickError) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The one item with the greatest key; Empty or Tie when there is not exactly one.
pub fn bag_max_by(_bag: Bag(a), by _by: fn(a) -> Int) -> Result(a, PickError) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The table without keys.
pub fn table_new() -> Table(k, v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// A table of the pairs; a later pair replaces an earlier one's value.
pub fn table_from_list(_pairs: List(#(k, v))) -> Table(k, v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The table with the key mapped to the value, replacing any value it had.
pub fn table_insert(_table: Table(k, v), _key: k, _value: v) -> Table(k, v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The table without the key.
pub fn table_remove(_table: Table(k, v), _key: k) -> Table(k, v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The key's value, if the table has the key.
pub fn table_get(_table: Table(k, v), _key: k) -> Option(v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The number of keys.
pub fn table_size(_table: Table(k, v)) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// The keys.
pub fn table_keys(_table: Table(k, v)) -> Bag(k) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The values, one occurrence per key.
pub fn table_values(_table: Table(k, v)) -> Bag(v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The entries that satisfy the predicate.
pub fn table_filter(
  _table: Table(k, v),
  keeping _keeping: fn(k, v) -> Bool,
) -> Table(k, v) {
  panic as "tazuna's built-ins run only in the engine"
}

/// Each value transformed, keys kept.
pub fn table_map(
  _table: Table(k, v),
  with _with: fn(k, v) -> w,
) -> Table(k, w) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The number of entries that satisfy the predicate.
pub fn table_count(_table: Table(k, v), where _where: fn(k, v) -> Bool) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// Whether some entry satisfies the predicate.
pub fn table_any(
  _table: Table(k, v),
  satisfying _satisfying: fn(k, v) -> Bool,
) -> Bool {
  panic as "tazuna's built-ins run only in the engine"
}

/// Whether every entry satisfies the predicate.
pub fn table_all(
  _table: Table(k, v),
  satisfying _satisfying: fn(k, v) -> Bool,
) -> Bool {
  panic as "tazuna's built-ins run only in the engine"
}

/// The date that many days later (earlier when negative).
pub fn date_add_days(_date: Date, _days: Int) -> Date {
  panic as "tazuna's built-ins run only in the engine"
}

/// The days from the first date to the second: negative when it is earlier.
pub fn date_days_between(from _from: Date, to _to: Date) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// `use <- tazuna.require(holds, rejection)`: the rest of the block when it holds, else the rejection.
pub fn require(
  _holds: Bool,
  _rejection: e,
  _then: fn() -> Result(a, e),
) -> Result(a, e) {
  panic as "tazuna's built-ins run only in the engine"
}

/// `use value <- tazuna.ref(table, key, rejection)`: the rest of the block with the key's value, else the rejection.
pub fn ref(
  _table: Table(k, v),
  _key: k,
  _rejection: e,
  _then: fn(v) -> Result(a, e),
) -> Result(a, e) {
  panic as "tazuna's built-ins run only in the engine"
}
// Built-ins end.
