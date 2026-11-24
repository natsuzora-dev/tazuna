//// Bags: multisets, whose items have no order.
////
//// Lean gives a spec its meaning, so the bodies here only let a spec
//// compile; Gleam never runs them.
////
//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`
//// in lean/. DO NOT EDIT.

/// A multiset: two bags are equal when each value occurs as often in both.
pub type Bag(a)

pub type PickError {
  Empty
  Tie
}

/// A bag of the list's items.
pub fn from_list(_items: List(a)) -> Bag(a) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The bag with one more occurrence of the item.
pub fn insert(_bag: Bag(a), _item: a) -> Bag(a) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The number of items, counting each occurrence.
pub fn size(_bag: Bag(a)) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// The items that satisfy the predicate.
pub fn filter(_bag: Bag(a), keeping _keeping: fn(a) -> Bool) -> Bag(a) {
  panic as "tazuna's built-ins run only in the engine"
}

/// Each item transformed, occurrences kept.
pub fn map(_bag: Bag(a), with _with: fn(a) -> b) -> Bag(b) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The number of items that satisfy the predicate.
pub fn count(_bag: Bag(a), where _where: fn(a) -> Bool) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// The sum of the function over the items.
pub fn sum(_bag: Bag(a), of _of: fn(a) -> Int) -> Int {
  panic as "tazuna's built-ins run only in the engine"
}

/// Whether some item satisfies the predicate.
pub fn any(_bag: Bag(a), satisfying _satisfying: fn(a) -> Bool) -> Bool {
  panic as "tazuna's built-ins run only in the engine"
}

/// Whether every item satisfies the predicate.
pub fn all(_bag: Bag(a), satisfying _satisfying: fn(a) -> Bool) -> Bool {
  panic as "tazuna's built-ins run only in the engine"
}

/// Whether the item occurs in the bag.
pub fn contains(_bag: Bag(a), _item: a) -> Bool {
  panic as "tazuna's built-ins run only in the engine"
}

/// The one item with the least key; Empty or Tie when there is not exactly one.
pub fn min_by(_bag: Bag(a), by _by: fn(a) -> Int) -> Result(a, PickError) {
  panic as "tazuna's built-ins run only in the engine"
}

/// The one item with the greatest key; Empty or Tie when there is not exactly one.
pub fn max_by(_bag: Bag(a), by _by: fn(a) -> Int) -> Result(a, PickError) {
  panic as "tazuna's built-ins run only in the engine"
}
