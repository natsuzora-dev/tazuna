import Tazuna.Ir.Builtin
import Tazuna.Semantics.Gleam
import Tazuna.Semantics.Value

/-! The meaning of each built-in. Bags are lists whose order no operation reveals; tables are lists of pairs whose keys
differ, which the type of a table demands. Every function here is generic over the values it holds, so the meaning of a built-in is the same at
every instance. -/

namespace Tazuna.Ir

namespace Builtin

/-- The one item whose key wins against every other: `none` reports an empty bag, `some none` a tie. -/
def pick {α : Type} (wins : Int → Int → Bool) (key : α → Int) : List α → Except Bool α
  | [] => .error false
  | x :: rest =>
    let best := rest.foldl (fun m y => if wins (key y) m then key y else m) (key x)
    match (x :: rest).filter (key · == best) with
    | [w] => .ok w
    | _ => .error true

def sumBy {α : Type} (f : α → Int) (xs : List α) : Int := (xs.map f).foldl (· + ·) 0

section Table
variable {k v : Sem}

/-- Whether `a` and `b` are the same key, asked both ways. -/
def sameKey (k : Sem) (a b : k.1) : Bool := k.2 a b || k.2 b a

def tableEmpty : (Sem.table k v).1 := ⟨[], .nil⟩

def tableRemove (key : k.1) (t : (Sem.table k v).1) : (Sem.table k v).1 :=
  ⟨t.1.filter (!sameKey k key ·.1), t.2.filter _⟩

/-- The table with `key` mapped to `value`: the old entry goes and the new one joins at the end. -/
def tableInsert (key : k.1) (value : v.1) (t : (Sem.table k v).1) : (Sem.table k v).1 :=
  ⟨(tableRemove key t).1 ++ [(key, value)], by
    refine List.pairwise_append.2 ⟨(tableRemove key t).2, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    simp only [tableRemove, List.mem_filter, sameKey, Bool.not_eq_true', Bool.or_eq_false_iff] at ha
    exact ⟨ha.2.2, ha.2.1⟩⟩

def tableFilter (keep : k.1 → v.1 → Bool) (t : (Sem.table k v).1) : (Sem.table k v).1 :=
  ⟨t.1.filter (fun e => keep e.1 e.2), t.2.filter _⟩

def tableMap {w : Sem} (f : k.1 → v.1 → w.1) (t : (Sem.table k v).1) : (Sem.table k w).1 :=
  ⟨t.1.map (fun e => (e.1, f e.1 e.2)), List.pairwise_map.2 (t.2.imp id)⟩

end Table

end Builtin

open Builtin

def Ty.ok {a e : Ty} (x : a.den) : (Ty.result a e).den := .inl (x, ())
def Ty.error {a e : Ty} (x : e.den) : (Ty.result a e).den := .inr (.inl (x, ()))
def Ty.some {a : Ty} (x : a.den) : (Ty.option a).den := .inl (x, ())
def Ty.none {a : Ty} : (Ty.option a).den := .inr (.inl ())

def Ty.ofPick {a : Ty} : Except Bool a.den → (Ty.result a .pickError).den
  | .ok x => Ty.ok x
  | .error false => Ty.error (e := .pickError) (.inl ())
  | .error true => Ty.error (e := .pickError) (.inr (.inl ()))

/-- The value of a built-in at the type arguments `args`. -/
def Prim.den : (p : Prim) → (args : List Ty) → (p.ty.inst args).den
  | .length, _ => fun (s, ()) => Gleam.length s
  | .bagFromList, _ => fun (xs, ()) => xs
  | .bagInsert, _ => fun (xs, x, ()) => x :: xs
  | .bagSize, _ => fun (xs, ()) => (xs.length : Int)
  | .bagFilter, _ => fun (xs, f, ()) => xs.filter fun x => Ty.toBool (f (x, ()))
  | .bagMap, _ => fun (xs, f, ()) => xs.map fun x => f (x, ())
  | .bagCount, _ => fun (xs, f, ()) => ((xs.filter fun x => Ty.toBool (f (x, ()))).length : Int)
  | .bagSum, _ => fun (xs, f, ()) => sumBy (fun x => f (x, ())) xs
  | .bagAny, _ => fun (xs, f, ()) => Ty.ofBool (xs.any fun x => Ty.toBool (f (x, ())))
  | .bagAll, _ => fun (xs, f, ()) => Ty.ofBool (xs.all fun x => Ty.toBool (f (x, ())))
  | .bagContains, args => fun (xs, x, ()) => Ty.ofBool (xs.any (Ty.deq (args[0]?.getD (.param 0)) x))
  | .bagMinBy, _ => fun (xs, f, ()) => Ty.ofPick (pick (· < ·) (fun x => f (x, ())) xs)
  | .bagMaxBy, _ => fun (xs, f, ()) => Ty.ofPick (pick (· > ·) (fun x => f (x, ())) xs)
  | .tableNew, _ => fun () => Builtin.tableEmpty
  | .tableFromList, _ => fun (pairs, ()) => pairs.foldl (fun t (k, v, ()) => Builtin.tableInsert k v t) tableEmpty
  | .tableInsert, _ => fun (t, k, v, ()) => Builtin.tableInsert k v t
  | .tableRemove, _ => fun (t, k, ()) => Builtin.tableRemove k t
  | .tableGet, args => fun (t, k, ()) => match lookupBy (Ty.deq (args[0]?.getD (.param 0))) k t.1 with
    | .some v => Ty.some v
    | .none => Ty.none
  | .tableSize, _ => fun (t, ()) => (t.1.length : Int)
  | .tableKeys, _ => fun (t, ()) => t.1.map (·.1)
  | .tableValues, _ => fun (t, ()) => t.1.map (·.2)
  | .tableFilter, _ => fun (t, f, ()) => Builtin.tableFilter (fun k v => Ty.toBool (f (k, v, ()))) t
  | .tableMap, _ => fun (t, f, ()) => Builtin.tableMap (fun k v => f (k, v, ())) t
  | .tableCount, _ => fun (t, f, ()) => ((t.1.filter fun (k, v) => Ty.toBool (f (k, v, ()))).length : Int)
  | .tableAny, _ => fun (t, f, ()) => Ty.ofBool (t.1.any fun (k, v) => Ty.toBool (f (k, v, ())))
  | .tableAll, _ => fun (t, f, ()) => Ty.ofBool (t.1.all fun (k, v) => Ty.toBool (f (k, v, ())))
  | .dateAddDays, _ => fun (d, n, ()) => @HAdd.hAdd Int Int Int _ d n
  | .dateDaysBetween, _ => fun (a, b, ()) => @HSub.hSub Int Int Int _ b a
  | .require, _ => fun (holds, rejection, next, ()) => if Ty.toBool holds then next () else Ty.error rejection
  | .ref, args => fun (t, k, rejection, next, ()) => match lookupBy (Ty.deq (args[0]?.getD (.param 0))) k t.1 with
    | .some v => next (v, ())
    | .none => Ty.error rejection

/-! Examples, one or more per built-in: what each means at a concrete instance. -/

section Examples
open Ty (ofBool toBool)

private def I (x : Int) : Int := x
private def pos (x : Int) : Ty.bool.den := ofBool (decide (0 < x))
private def isOk {a e : Ty} : (Ty.result a e).den → Option a.den
  | .inl (x, ()) => .some x
  | .inr _ => .none
private def pickFailure {a : Ty} : (Ty.result a .pickError).den → Option Bool
  | .inr (.inl (.inl (), ())) => .some false
  | .inr (.inl (.inr _, ())) => .some true
  | .inl _ => .none
private def table : (Ty.table .int .str).den := ⟨[((1 : Int), "a"), ((2 : Int), "bb")], by simp [KeysUnique, Ty.sem]⟩

example : Prim.length.den [] ("e\u0301", ()) = (2 : Int) := rfl
example : Prim.bagFromList.den [.int] (([1, 1, 2] : List Int), ()) = ([1, 1, 2] : List Int) := rfl
example : Prim.bagInsert.den [.int] (([1] : List Int), (1 : Int), ()) = ([1, 1] : List Int) := rfl
example : Prim.bagSize.den [.int] (([1, 1, 2] : List Int), ()) = (3 : Int) := rfl
example : Prim.bagFilter.den [.int] (([-1, 2, 3] : List Int), fun (x, ()) => pos x, ()) = ([2, 3] : List Int) := rfl
example : Prim.bagMap.den [.int, .str] (([1, 1] : List Int), fun (x, ()) => toString (I x), ()) = ["1", "1"] := rfl
example : Prim.bagCount.den [.int] (([-1, 2, 3] : List Int), fun (x, ()) => pos x, ()) = (2 : Int) := rfl
example : Prim.bagSum.den [.int] (([1, 2, 3] : List Int), fun (x, ()) => I x * 10, ()) = (60 : Int) := rfl
example : toBool (Prim.bagAny.den [.int] (([-1, 2] : List Int), fun (x, ()) => pos x, ())) = true := rfl
example : toBool (Prim.bagAll.den [.int] (([-1, 2] : List Int), fun (x, ()) => pos x, ())) = false := rfl
example : toBool (Prim.bagContains.den [.int] (([1, 2] : List Int), (2 : Int), ())) = true := rfl
-- One least key picks its item; an empty bag is Empty and a shared least key is Tie, whatever the order.
example : isOk (Prim.bagMinBy.den [.str] ((["bb", "a"] : List String), fun (s, ()) => (s.length : Int), ())) = .some "a" := rfl
example : pickFailure (Prim.bagMinBy.den [.str] (([] : List String), fun (s, ()) => (s.length : Int), ())) = .some false := rfl
example : pickFailure (Prim.bagMinBy.den [.str] ((["a", "b"] : List String), fun (s, ()) => (s.length : Int), ())) = .some true := rfl
example : isOk (Prim.bagMaxBy.den [.str] ((["bb", "a"] : List String), fun (s, ()) => (s.length : Int), ())) = .some "bb" := rfl
example : (Prim.tableNew.den [.int, .str] ()).1 = ([] : List (Int × String)) := rfl
-- A later pair replaces an earlier one's value.
example : (Prim.tableFromList.den [.int, .str] (([((1 : Int), "a", ()), ((1 : Int), "b", ())] : List (Int × String × Unit)), ())).1 = ([(1, "b")] : List (Int × String)) := rfl
example : (Prim.tableInsert.den [.int, .str] (table, (1 : Int), "c", ())).1 = ([(2, "bb"), (1, "c")] : List (Int × String)) := rfl
example : (Prim.tableInsert.den [.int, .str] (table, (3 : Int), "c", ())).1 = ([(1, "a"), (2, "bb"), (3, "c")] : List (Int × String)) := rfl
example : (Prim.tableRemove.den [.int, .str] (table, (1 : Int), ())).1 = ([(2, "bb")] : List (Int × String)) := rfl
example : Prim.tableGet.den [.int, .str] (table, (2 : Int), ()) = Ty.some (a := .str) "bb" := rfl
example : Prim.tableGet.den [.int, .str] (table, (3 : Int), ()) = Ty.none (a := .str) := rfl
example : Prim.tableSize.den [.int, .str] (table, ()) = (2 : Int) := rfl
example : Prim.tableKeys.den [.int, .str] (table, ()) = ([1, 2] : List Int) := rfl
example : Prim.tableValues.den [.int, .str] (table, ()) = ["a", "bb"] := rfl
example : (Prim.tableFilter.den [.int, .str] (table, fun (k, _, ()) => pos (I k - 1), ())).1 = ([(2, "bb")] : List (Int × String)) := rfl
example : (Prim.tableMap.den [.int, .str, .int] (table, fun (_, v, ()) => (v.length : Int), ())).1 =
  ([(1, 1), (2, 2)] : List (Int × Int)) := rfl
example : Prim.tableCount.den [.int, .str] (table, fun (k, _, ()) => pos k, ()) = (2 : Int) := rfl
example : toBool (Prim.tableAny.den [.int, .str] (table, fun (k, _, ()) => pos (I k - 1), ())) = true := rfl
example : toBool (Prim.tableAll.den [.int, .str] (table, fun (k, _, ()) => pos (I k - 1), ())) = false := rfl
example : Prim.dateAddDays.den [] ((100 : Int), (-3 : Int), ()) = (97 : Int) := rfl
example : Prim.dateDaysBetween.den [] ((100 : Int), (97 : Int), ()) = (-3 : Int) := rfl
-- `use <- require(holds, r)` continues when it holds and rejects with r otherwise.
example : isOk (Prim.require.den [.int, .str] (ofBool true, "r", fun () => Ty.ok (e := .str) (1 : Int), ()))
  = .some (1 : Int) := rfl
example : Prim.require.den [.int, .str] (ofBool false, "r", fun () => Ty.ok (e := .str) (1 : Int), ()) =
  Ty.error (a := .int) (e := .str) "r" := rfl
-- `use v <- ref(table, key, r)` continues with the key's value and rejects with r when the key is absent.
example : isOk (Prim.ref.den [.int, .str, .str, .str] (table, (2 : Int), "r", fun (v, ()) => Ty.ok (e := .str) v, ()))
  = .some "bb" := rfl
example : Prim.ref.den [.int, .str, .str, .str] (table, (3 : Int), "r", fun (v, ()) => Ty.ok (e := .str) v, ()) =
  Ty.error (a := .str) (e := .str) "r" := rfl

end Examples

end Tazuna.Ir
