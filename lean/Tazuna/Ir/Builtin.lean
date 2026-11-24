import Tazuna.Ir.Surface
import Tazuna.Ir.Ty

/-! Everything the `tazuna` Gleam module declares: its types, its aliases and its built-in functions. This table is the
one source: elaboration reads the signatures, `Tazuna.Semantics.Builtin` gives each function its meaning, and
`lake exe gen-dsl` writes the Gleam declarations, whose bodies only panic. The set stays general: no calendars, time
zones or formats. -/

namespace Tazuna.Ir

/-- A type `tazuna` declares without variants: Lean gives it a meaning of its own. -/
structure OpaqueType where
  name : String
  params : List String
  doc : String
  make : List Ty → Option Ty

def opaqueTypes : List OpaqueType :=
  [ ⟨"Bag", ["a"], "A multiset: two bags are equal when each value occurs as often in both.",
      fun | [t] => some (.bag t) | _ => none⟩,
    ⟨"Table", ["k", "v"], "A finite map from keys to values; at most one value per key.",
      fun | [k, v] => some (.table k v) | _ => none⟩,
    ⟨"Date", [], "A day. Dates have no calendar: a spec adds days and counts the days between two dates.",
      fun | [] => some .date | _ => none⟩,
    ⟨"Id", [], "An identifier a step makes fresh; ids compare with `==` only.",
      fun | [] => some .id | _ => none⟩ ]

/-- The type `tazuna.<name>` at `args`, when `tazuna` declares it opaque. -/
def opaqueTy? (name : String) (args : List Ty) : Option Ty :=
  match name.dropPrefix? "tazuna." with
  | some n => (opaqueTypes.find? (·.name == n.toString)).bind (·.make args)
  | none => none

/-- Aliases `tazuna` declares, with their documentation. -/
def builtinAliases : List (Surface.AliasDef × String) :=
  [ (⟨"tazuna.Instant", [], .con "Int" [], ⟨0, 0⟩⟩, "A point in time, in milliseconds."),
    (⟨"tazuna.Duration", [], .con "Int" [], ⟨0, 0⟩⟩, "A length of time, in milliseconds.") ]

/-- The built-in functions. -/
inductive Prim where
  | length
  | bagFromList | bagInsert | bagSize | bagFilter | bagMap | bagCount | bagSum | bagAny | bagAll | bagContains
  | bagMinBy | bagMaxBy
  | tableNew | tableFromList | tableInsert | tableRemove | tableGet | tableSize | tableKeys | tableValues
  | tableFilter | tableMap | tableCount | tableAny | tableAll
  | dateAddDays | dateDaysBetween
  | require | ref
deriving Repr, DecidableEq

structure PrimParam where
  label : Option String
  name : String
  ty : Ty

structure PrimSig where
  name : String
  doc : String
  tvars : List String
  params : List PrimParam
  ret : Ty
  /-- The type variables `==` must work on (`Ty.comparable`), by index. -/
  needsEq : List Nat := []

namespace Prim

open Ty in
def sig : Prim → PrimSig :=
  let a := param 0
  let b := param 1
  let k := param 0
  let v := param 1
  let p (n : String) (t : Ty) : PrimParam := ⟨none, n, t⟩
  let l (lab : String) (t : Ty) : PrimParam := ⟨some lab, lab, t⟩
  fun
  | .length => ⟨"length", "The number of code points.", [], [p "string" .str], .int, []⟩
  | .bagFromList => ⟨"bag_from_list", "A bag of the list's items.", ["a"], [p "items" (.list a)], .bag a, []⟩
  | .bagInsert => ⟨"bag_insert", "The bag with one more occurrence of the item.", ["a"],
      [p "bag" (.bag a), p "item" a], .bag a, []⟩
  | .bagSize => ⟨"bag_size", "The number of items, counting each occurrence.", ["a"], [p "bag" (.bag a)], .int, []⟩
  | .bagFilter => ⟨"bag_filter", "The items that satisfy the predicate.", ["a"],
      [p "bag" (.bag a), l "keeping" (.fn [a] .bool)], .bag a, []⟩
  | .bagMap => ⟨"bag_map", "Each item transformed, occurrences kept.", ["a", "b"],
      [p "bag" (.bag a), l "with" (.fn [a] b)], .bag b, []⟩
  | .bagCount => ⟨"bag_count", "The number of items that satisfy the predicate.", ["a"],
      [p "bag" (.bag a), l "where" (.fn [a] .bool)], .int, []⟩
  | .bagSum => ⟨"bag_sum", "The sum of the function over the items.", ["a"],
      [p "bag" (.bag a), l "of" (.fn [a] .int)], .int, []⟩
  | .bagAny => ⟨"bag_any", "Whether some item satisfies the predicate.", ["a"],
      [p "bag" (.bag a), l "satisfying" (.fn [a] .bool)], .bool, []⟩
  | .bagAll => ⟨"bag_all", "Whether every item satisfies the predicate.", ["a"],
      [p "bag" (.bag a), l "satisfying" (.fn [a] .bool)], .bool, []⟩
  | .bagContains => ⟨"bag_contains", "Whether the item occurs in the bag.", ["a"],
      [p "bag" (.bag a), p "item" a], .bool, [0]⟩
  | .bagMinBy => ⟨"bag_min_by", "The one item with the least key; Empty or Tie when there is not exactly one.",
      ["a"], [p "bag" (.bag a), l "by" (.fn [a] .int)], .result a .pickError, []⟩
  | .bagMaxBy => ⟨"bag_max_by", "The one item with the greatest key; Empty or Tie when there is not exactly one.",
      ["a"], [p "bag" (.bag a), l "by" (.fn [a] .int)], .result a .pickError, []⟩
  | .tableNew => ⟨"table_new", "The table without keys.", ["k", "v"], [], .table k v, [0]⟩
  | .tableFromList => ⟨"table_from_list", "A table of the pairs; a later pair replaces an earlier one's value.",
      ["k", "v"], [p "pairs" (.list (.tuple [k, v]))], .table k v, [0]⟩
  | .tableInsert => ⟨"table_insert", "The table with the key mapped to the value, replacing any value it had.",
      ["k", "v"], [p "table" (.table k v), p "key" k, p "value" v], .table k v, [0]⟩
  | .tableRemove => ⟨"table_remove", "The table without the key.", ["k", "v"],
      [p "table" (.table k v), p "key" k], .table k v, [0]⟩
  | .tableGet => ⟨"table_get", "The key's value, if the table has the key.", ["k", "v"],
      [p "table" (.table k v), p "key" k], .option v, [0]⟩
  | .tableSize => ⟨"table_size", "The number of keys.", ["k", "v"], [p "table" (.table k v)], .int, []⟩
  | .tableKeys => ⟨"table_keys", "The keys.", ["k", "v"], [p "table" (.table k v)], .bag k, []⟩
  | .tableValues => ⟨"table_values", "The values, one occurrence per key.", ["k", "v"],
      [p "table" (.table k v)], .bag v, []⟩
  | .tableFilter => ⟨"table_filter", "The entries that satisfy the predicate.", ["k", "v"],
      [p "table" (.table k v), l "keeping" (.fn [k, v] .bool)], .table k v, []⟩
  | .tableMap => ⟨"table_map", "Each value transformed, keys kept.", ["k", "v", "w"],
      [p "table" (.table k v), l "with" (.fn [k, v] (param 2))], .table k (param 2), []⟩
  | .tableCount => ⟨"table_count", "The number of entries that satisfy the predicate.", ["k", "v"],
      [p "table" (.table k v), l "where" (.fn [k, v] .bool)], .int, []⟩
  | .tableAny => ⟨"table_any", "Whether some entry satisfies the predicate.", ["k", "v"],
      [p "table" (.table k v), l "satisfying" (.fn [k, v] .bool)], .bool, []⟩
  | .tableAll => ⟨"table_all", "Whether every entry satisfies the predicate.", ["k", "v"],
      [p "table" (.table k v), l "satisfying" (.fn [k, v] .bool)], .bool, []⟩
  | .dateAddDays => ⟨"date_add_days", "The date that many days later (earlier when negative).", [],
      [p "date" .date, p "days" .int], .date, []⟩
  | .dateDaysBetween => ⟨"date_days_between", "The days from the first date to the second: negative when it is earlier.",
      [], [l "from" .date, l "to" .date], .int, []⟩
  | .require => ⟨"require",
      "`use <- tazuna.require(holds, rejection)`: the rest of the block when it holds, else the rejection.",
      ["a", "e"], [p "holds" .bool, p "rejection" (param 1), p "then" (.fn [] (.result a (param 1)))],
      .result a (param 1), []⟩
  | .ref => ⟨"ref",
      "`use value <- tazuna.ref(table, key, rejection)`: the rest of the block with the key's value, else the rejection.",
      ["k", "v", "a", "e"],
      [p "table" (.table k v), p "key" k, p "rejection" (param 3), p "then" (.fn [v] (.result (param 2) (param 3)))],
      .result (param 2) (param 3), [0]⟩

def all : List Prim :=
  [.length, .bagFromList, .bagInsert, .bagSize, .bagFilter, .bagMap, .bagCount, .bagSum, .bagAny, .bagAll,
   .bagContains, .bagMinBy, .bagMaxBy, .tableNew, .tableFromList, .tableInsert, .tableRemove, .tableGet, .tableSize,
   .tableKeys, .tableValues, .tableFilter, .tableMap, .tableCount, .tableAny, .tableAll, .dateAddDays,
   .dateDaysBetween, .require, .ref]

theorem mem_all (p : Prim) : p ∈ all := by cases p <;> simp [all]

/-- The generic type, with `param k` for the `k`-th type variable. -/
def ty (p : Prim) : Ty := .fn (p.sig.params.map (·.ty)) p.sig.ret

def labels (p : Prim) : List (Option String) := p.sig.params.map (·.label)

/-- Whether the type arguments meet the signature's demands. -/
def ok (p : Prim) (args : List Ty) : Bool :=
  args.length == p.sig.tvars.length && p.sig.needsEq.all fun k => (args[k]?.map Ty.comparable).getD false

/-- The built-in a global name such as `tazuna.bag_filter` refers to. -/
def byName? (name : String) : Option Prim :=
  match name.dropPrefix? "tazuna." with
  | some n => all.find? (·.sig.name == n.toString)
  | none => none

end Prim

end Tazuna.Ir
