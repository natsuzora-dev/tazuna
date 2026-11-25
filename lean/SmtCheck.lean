import Tazuna.Smt.Step
import Tazuna.Smt.Prove
import Tazuna.Semantics.After
import Tazuna.Smt.Bounds
import Tazuna.Smt.Solver
import Tazuna.Smt.ServiceLayout
import Tazuna.Smt.FiresForward

-- Test scaffolding: a value the model leaves out reads as a default that the checks then reject.
set_option linter.tazuna.silentDefault false

/-! Runs the solver on printed scripts and reads its answers back: the theorems cover printing and reading our own
text, and this check covers what only the solver can say, that it reads the text as SMT-LIB and prints values the
reader reads. Each case encodes a closed expression, asks the solver for a variable equal to it, and compares the
value, decoded, with `eval`. Usage: smt-check <z3 executable>. -/

open Tazuna.Ir Tazuna.Smt

/-- The cases read slots by `S[j]!`, which a case's layout always has. -/
instance {w : Nat} : Inhabited (SlotItems w) := ⟨⟨List.replicate w tt, by simp⟩⟩

abbrev E (t : Ty) := Expr [] [] t

def optI : Ty := Ty.option .int
/-- A record with two variants that share an Int field `id` at index 0. -/
def shape : Ty := .adt 8 [] [[.int, .str], [.int]]

def tru : E Ty.bool := .ctor ⟨0, by decide⟩ .nil
def some5 : E optI := .ctor (vs := [[.int], []]) ⟨0, by decide⟩ (.cons (.int 5) .nil)
def none' : E optI := .ctor (vs := [[.int], []]) ⟨1, by decide⟩ .nil

/-- `case o { Some(x) if x > 3 -> x * 2  Some(x) -> x  None -> 0 }` -/
def guarded (o : E optI) : E .int :=
  .case o
    (.guarded (.ctor (vs := [[.int], []]) ⟨0, by decide⟩ (.cons .bind .nil)) (.bin .gt (.var .here) (.int 3))
      (.bin .mul (.var .here) (.int 2))
      (.cons (.ctor (vs := [[.int], []]) ⟨0, by decide⟩ (.cons .bind .nil)) (.var .here)
        (.cons (.ctor (vs := [[.int], []]) ⟨1, by decide⟩ .nil) (.int 0) .nil)))
    ⟨10, rfl⟩

def circle : E shape := .ctor ⟨1, by decide⟩ (.cons (.int 7) .nil)
def square : E shape := .ctor ⟨0, by decide⟩ (.cons (.int 3) (.cons (.str "sq") .nil))

/-- `bag.from_list([1, 2, 2])` -/
def b3 : E (.bag .int) :=
  .call (.prim .bagFromList [.int] rfl) (.cons (.list (.cons (.int 1) (.cons (.int 2) (.cons (.int 2) .nil)))) .nil)
def bagOp (p : Prim) (r : Ty) (h : p.ok [.int] = true) (hty : p.ty.inst [.int] = .fn [.bag .int, .fn [.int] Ty.bool] r)
    (b : E (.bag .int)) (body : Expr [] [.int] Ty.bool) : E r :=
  .call (hty ▸ (Expr.prim p [.int] h : E (p.ty.inst [.int])) : E (.fn [.bag .int, .fn [.int] Ty.bool] r))
    (.cons b (.cons (Expr.lam (ps := [.int]) body) .nil))
def bagSum (b : E (.bag .int)) (body : Expr [] [.int] .int) : E .int :=
  .call (.prim .bagSum [.int] rfl) (.cons b (.cons (.lam body) .nil))
def bagMap (b : E (.bag .int)) (r : Ty) (h : Prim.bagMap.ok [.int, r] = true) (body : Expr [] [.int] r) : E (.bag r) :=
  .call (.prim .bagMap [.int, r] h) (.cons b (.cons (.lam body) .nil))
def bagContains (t : Ty) (h : Prim.bagContains.ok [t] = true) (b : E (.bag t)) (x : E t) : E Ty.bool :=
  .call (.prim .bagContains [t] h) (.cons b (.cons x .nil))
def bagSize (t : Ty) (h : Prim.bagSize.ok [t] = true) (b : E (.bag t)) : E .int := .call (.prim .bagSize [t] h) (.cons b .nil)
def minBy (b : E (.bag .int)) (body : Expr [] [.int] .int) : E (Ty.result .int Ty.pickError) :=
  .call (.prim .bagMinBy [.int] rfl) (.cons b (.cons (.lam body) .nil))
def maxBy (b : E (.bag .int)) (body : Expr [] [.int] .int) : E (Ty.result .int Ty.pickError) :=
  .call (.prim .bagMaxBy [.int] rfl) (.cons b (.cons (.lam body) .nil))
def b0 : E (.bag .int) := .call (.prim .bagFromList [.int] rfl) (.cons (.list .nil) .nil)
def bagOf (xs : List Int) : E (.bag .int) :=
  .call (.prim .bagFromList [.int] rfl) (.cons (.list (xs.foldr (fun x r => .cons (.int x) r) .nil)) .nil)
def isTwo : Expr [] [.int] Ty.bool := .bin (.eq rfl) (.var .here) (.int 2)
def bigger : Expr [] [.int] Ty.bool := .bin .gt (.var .here) (.int 1)
/-- `table.from_list([#(1, "a"), #(1, "c")])`: the last pair for key 1 wins. -/
def t2 : E (.table .int .str) :=
  let pair (k : Int) (v : String) : Expr [] [] (.tuple [.int, .str]) := .tuple (.cons (.int k) (.cons (.str v) .nil))
  .call (.prim .tableFromList [.int, .str] rfl)
    (.cons (.list (.cons (pair 1 "a") (.cons (pair 1 "c") .nil))) .nil)
def tableAnyV (t : E (.table .int .str)) (v : String) : E Ty.bool :=
  .call (.prim .tableAny [.int, .str] rfl)
    (.cons t (.cons (.lam (.bin (.eq rfl) (.var (.there .here)) (.str v))) .nil))
def tableSize (t : E (.table .int .str)) : E .int := .call (.prim .tableSize [.int, .str] rfl) (.cons t .nil)

/-- `n` inserts into a new table, cycling through three keys, so the table stays within its three slots. As trees,
the terms would grow about seventyfold per insert; shared, the script grows by one definition per insert. -/
def inserts : Nat → E (.table .int .str)
  | 0 => .call (.prim .tableNew [.int, .str] rfl) .nil
  | n + 1 => .call (.prim .tableInsert [.int, .str] rfl)
    (.cons (inserts n) (.cons (.int (n % 3)) (.cons (.str s!"v{n}") .nil)))
/-- `let x = 1; let x = x + x; ...`, `n` times: a tree of `2 ^ n` leaves, a script of `n` definitions. -/
def doubling : Nat → (Γ : List Ty) → Expr [] Γ .int
  | 0, _ => .int 1
  | n + 1, Γ => .let_ (doubling n Γ) (.bin .add (.var .here) (.var .here))

def tableKeys (t : E (.table .int .str)) : E (.bag .int) := .call (.prim .tableKeys [.int, .str] rfl) (.cons t .nil)
def tableValues (t : E (.table .int .str)) : E (.bag .str) := .call (.prim .tableValues [.int, .str] rfl) (.cons t .nil)
/-- `table.map(t, fn(k, v) { v <> "!" })` -/
def tableBang (t : E (.table .int .str)) : E (.table .int .str) :=
  .call (.prim .tableMap [.int, .str, .str] rfl)
    (.cons t (.cons (.lam (.bin .concat (.var (.there .here)) (.str "!"))) .nil))
/-- `bag.from_list([1, 5])` -/
def b2 : E (.bag .int) :=
  .call (.prim .bagFromList [.int] rfl) (.cons (.list (.cons (.int 1) (.cons (.int 5) .nil))) .nil)

def tableOf (kvs : List (Int × String)) : E (.table .int .str) :=
  let pair (k : Int) (v : String) : Expr [] [] (.tuple [.int, .str]) := .tuple (.cons (.int k) (.cons (.str v) .nil))
  .call (.prim .tableFromList [.int, .str] rfl) (.cons (.list (kvs.foldr (fun (k, v) r => .cons (pair k v) r) .nil)) .nil)
def tableGet (t : E (.table .int .str)) (k : Int) : E (Ty.option .str) :=
  .call (.prim .tableGet [.int, .str] rfl) (.cons t (.cons (.int k) .nil))
/-- `use v <- ref(t, k, "no")` continuing with `Ok(v)`. -/
def refOk (t : E (.table .int .str)) (k : Int) : E (Ty.result .str .str) :=
  .call (.prim .tableLookup [.int, .str, .str, .str] rfl) (.cons t (.cons (.int k) (.cons (.str "no")
    (.cons (.lam (.ctor (vs := [[.str], [.str]]) ⟨0, by decide⟩ (.cons (.var .here) .nil))) .nil))))

/-- `case o { Some(x) -> [x, x + 1]  None -> [] }`: branches of different lengths share the list's two slots. -/
def twoOrNone (o : E optI) : E (.list .int) :=
  .case o
    (.cons (.ctor (vs := [[.int], []]) ⟨0, by decide⟩ (.cons .bind .nil))
      (.list (.cons (.var .here) (.cons (.bin .add (.var .here) (.int 1)) .nil)))
      (.cons (.ctor (vs := [[.int], []]) ⟨1, by decide⟩ .nil) (.list .nil) .nil))
    ⟨10, rfl⟩

/-- `Ok(twoOrNone(o))`: a list inside a constructor, as a command's `decide` returns its events. -/
def okList (o : E optI) : E (Ty.result (.list .int) .str) :=
  .ctor (vs := [[.list .int], [.str]]) ⟨0, by decide⟩ (.cons (twoOrNone o) .nil)

/-- `table.from_list` of pairs a case chooses, so free slots of the list are skipped. -/
def tableOfCase (o : E optI) : E (.table .int .str) :=
  let pair (k : Int) (v : String) : Expr [] [] (.tuple [.int, .str]) := .tuple (.cons (.int k) (.cons (.str v) .nil))
  .call (.prim .tableFromList [.int, .str] rfl)
    (.cons (.case o
      (.cons (.ctor (vs := [[.int], []]) ⟨0, by decide⟩ (.cons .wild .nil))
        (.list (.cons (pair 1 "a") (.cons (pair 2 "b") (.cons (pair 1 "c") .nil))))
        (.cons (.ctor (vs := [[.int], []]) ⟨1, by decide⟩ .nil) (.list (.cons (pair 4 "d") .nil)) .nil))
      ⟨10, rfl⟩) .nil)

def listCases : List (String × (t : Ty) × E t) :=
  [ ("a list keeps its order", ⟨.list .int, .list (.cons (.int 3) (.cons (.int 1) (.cons (.int 2) .nil)))⟩),
    ("the longer branch of a list case", ⟨.list .int, twoOrNone some5⟩),
    ("the empty branch of a list case", ⟨.list .int, twoOrNone none'⟩),
    ("a list inside a constructor", ⟨Ty.result (.list .int) .str, okList some5⟩),
    ("a bag from a list case", ⟨.bag .int, .call (.prim .bagFromList [.int] rfl) (.cons (twoOrNone some5) .nil)⟩),
    ("a table from the longer list", ⟨.table .int .str, tableOfCase some5⟩),
    ("a table from the shorter list", ⟨.table .int .str, tableOfCase none'⟩) ]

def cases : List (String × (t : Ty) × E t) :=
  [ ("truncating division", ⟨.int, .bin .div (.int (-7)) (.int 2)⟩),
    ("division by a negative", ⟨.int, .bin .div (.int 7) (.int (-2))⟩),
    ("division by zero", ⟨.int, .bin .div (.int 7) (.int 0)⟩),
    ("remainder of a negative", ⟨.int, .bin .mod (.int (-7)) (.int 2)⟩),
    ("remainder by a negative", ⟨.int, .bin .mod (.int 7) (.int (-2))⟩),
    ("remainder by zero", ⟨.int, .bin .mod (.int 7) (.int 0)⟩),
    ("negation", ⟨.int, .neg (.bin .mul (.int 3) (.int 4))⟩),
    ("let", ⟨.int, .let_ (.int 5) (.bin .add (.var .here) (.var .here))⟩),
    ("comparison", ⟨Ty.bool, .bin .and (.bin .lt (.int 1) (.int 2)) (.not (.bin .ge (.int 1) (.int 2)))⟩),
    ("string escapes", ⟨.str, .bin .concat (.str "quote \" backslash \\ ") (.str "tab\tnewline\né 😀")⟩),
    ("string equality", ⟨Ty.bool, .bin (.ne rfl) (.str "a") (.str "b")⟩),
    ("Bool literal", ⟨Ty.bool, .bin .or (.not tru) tru⟩),
    ("Option constructor", ⟨optI, some5⟩),
    ("== on Options", ⟨Ty.bool, .bin (.eq rfl) some5 none'⟩),
    ("guard taken", ⟨.int, guarded some5⟩),
    ("guard not taken", ⟨.int, guarded (.ctor (vs := [[.int], []]) ⟨0, by decide⟩ (.cons (.int 2) .nil))⟩),
    ("no clause binds", ⟨.int, guarded none'⟩),
    ("shared field of another variant", ⟨.int, .field "id" 0 (fun fs h => by simp at h; rcases h with rfl | rfl <;> rfl) circle⟩),
    ("tuple index", ⟨.str, .index (.tuple (.cons (.int 1) (.cons (.str "a") .nil))) ⟨1, by decide⟩⟩),
    ("tuple value", ⟨.tuple [.int, Ty.bool], .tuple (.cons (.int 1) (.cons tru .nil))⟩),
    ("record update", ⟨.adt 9 [] [[.int, .str]],
      .update (.ctor ⟨0, by decide⟩ (.cons (.int 1) (.cons (.str "a") .nil))) (.keep (.set (.str "b") .nil))⟩),
    ("lambda call", ⟨.int, .call (.lam (.bin .add (.var .here) (.var (.there .here)))) (.cons (.int 2) (.cons (.int 40) .nil))⟩),
    ("case on a record", ⟨.str, .case square
      (.cons (.ctor (vs := [[.int, .str], [.int]]) ⟨0, by decide⟩ (.cons .wild (.cons .bind .nil))) (.var .here)
        (.cons (.ctor (vs := [[.int, .str], [.int]]) ⟨1, by decide⟩ (.cons .wild .nil)) (.str "circle") .nil))
      ⟨10, rfl⟩⟩),
    ("length counts code points", ⟨.int, .call (.prim .length [] rfl) (.cons (.str "e\u0301😀a") .nil)⟩),
    ("require rejects", ⟨Ty.result .int .str, .call (.prim .require [.int, .str] rfl)
      (.cons (.bin .lt (.int 2) (.int 1)) (.cons (.str "no")
        (.cons (.lam (.ctor (vs := [[.int], [.str]]) ⟨0, by decide⟩ (.cons (.int 1) .nil))) .nil)))⟩),
    ("bag size counts occurrences", ⟨.int, .call (.prim .bagSize [.int] rfl) (.cons b3 .nil)⟩),
    ("bag count", ⟨.int, bagOp .bagCount .int rfl rfl b3 isTwo⟩),
    ("bag filter", ⟨.int, .call (.prim .bagSize [.int] rfl) (.cons (bagOp .bagFilter (.bag .int) rfl rfl b3 bigger) .nil)⟩),
    ("bag any", ⟨Ty.bool, bagOp .bagAny Ty.bool rfl rfl b3 isTwo⟩),
    ("bag sum counts occurrences", ⟨.int, bagSum b3 (.bin .mul (.var .here) (.int 10))⟩),
    ("min by picks the one least key", ⟨Ty.result .int Ty.pickError, minBy b3 (.var .here)⟩),
    ("max by reports a tie", ⟨Ty.result .int Ty.pickError, maxBy b3 (.var .here)⟩),
    ("max by with a negated key", ⟨Ty.result .int Ty.pickError, maxBy b3 (.neg (.var .here))⟩),
    ("min by of an empty bag", ⟨Ty.result .int Ty.pickError, minBy b0 (.var .here)⟩),
    ("bag map keeps occurrences", ⟨.int, bagSum (bagMap b3 .int rfl (.bin .mul (.var .here) (.int 10))) (.var .here)⟩),
    ("bag map transforms items", ⟨Ty.bool, .bin .and (bagContains .int rfl (bagMap b3 .int rfl (.bin .mul (.var .here) (.int 10))) (.int 20))
      (.not (bagContains .int rfl (bagMap b3 .int rfl (.bin .mul (.var .here) (.int 10))) (.int 2)))⟩),
    ("bag contains", ⟨Ty.bool, .bin .and (.call (.prim .bagContains [.int] rfl) (.cons b3 (.cons (.int 2) .nil)))
      (.not (.call (.prim .bagContains [.int] rfl) (.cons b3 (.cons (.int 5) .nil))))⟩),
    ("bag all", ⟨Ty.bool, bagOp .bagAll Ty.bool rfl rfl b3 bigger⟩),
    ("table from list replaces a key", ⟨.int, tableSize t2⟩),
    ("table keeps the last value", ⟨Ty.bool, .bin .and (tableAnyV t2 "c") (.not (tableAnyV t2 "a"))⟩),
    ("table remove", ⟨.int, tableSize (.call (.prim .tableRemove [.int, .str] rfl) (.cons t2 (.cons (.int 1) .nil)))⟩),
    ("table insert into new", ⟨.int, tableSize (.call (.prim .tableInsert [.int, .str] rfl)
      (.cons (.call (.prim .tableNew [.int, .str] rfl) .nil) (.cons (.int 5) (.cons (.str "x") .nil))))⟩),
    ("table keys", ⟨Ty.bool, .bin .and (bagContains .int rfl (tableKeys t2) (.int 1)) (.bin (.eq rfl) (bagSize .int rfl (tableKeys t2)) (.int 1))⟩),
    ("table values", ⟨Ty.bool, .bin .and (bagContains .str rfl (tableValues t2) (.str "c")) (.not (bagContains .str rfl (tableValues t2) (.str "a")))⟩),
    ("table map keeps keys", ⟨Ty.option .str, tableGet (tableBang t2) 1⟩),
    ("== on bags ignores order", ⟨Ty.bool, .bin (.eq rfl) b3 (bagOf [2, 1, 2])⟩),
    ("== on bags counts occurrences", ⟨Ty.bool, .bin (.eq rfl) b3 (bagOf [1, 1, 2])⟩),
    ("!= on bags of other sizes", ⟨Ty.bool, .bin (.ne rfl) b3 (bagOf [1, 2])⟩),
    ("bag map equals its image", ⟨Ty.bool, .bin (.eq rfl) (bagMap b3 .int rfl (.bin .mul (.var .here) (.int 10))) (bagOf [20, 10, 20])⟩),
    ("== on tables", ⟨Ty.bool, .bin (.eq rfl) t2 (tableOf [(1, "c")])⟩),
    ("== on tables compares values", ⟨Ty.bool, .bin (.eq rfl) t2 (tableOf [(1, "a")])⟩),
    ("!= on tables of other sizes", ⟨Ty.bool, .bin (.ne rfl) t2 (tableOf [(1, "c"), (2, "d")])⟩),
    ("table get finds the key", ⟨Ty.option .str, tableGet t2 1⟩),
    ("table get misses a key", ⟨Ty.option .str, tableGet t2 5⟩),
    ("ref continues with the value", ⟨Ty.result .str .str, refOk t2 1⟩),
    ("ref rejects a missing key", ⟨Ty.result .str .str, refOk t2 5⟩),
    ("twelve inserts share their tables", ⟨Ty.bool, tableAnyV (inserts 12) "v11"⟩),
    ("forty lets share their values", ⟨.int, doubling 40 []⟩),
    ("require passes", ⟨Ty.result .int .str, .call (.prim .require [.int, .str] rfl)
      (.cons (.bin .lt (.int 1) (.int 2)) (.cons (.str "no")
        (.cons (.lam (.ctor (vs := [[.int], [.str]]) ⟨0, by decide⟩ (.cons (.int 1) .nil))) .nil)))⟩) ]

/-- Slot counts that differ by item type, so maps and keys carry slots into a collection of another count: bags of
Bool get two slots, bags of String four, the rest three. -/
def reslots : Ty → Nat
  | .bag (.adt 0 _ _) => 2
  | .bag .str => 4
  | _ => 3

def reslotted : List (String × (t : Ty) × E t) :=
  [ ("map into fewer slots", ⟨.int, bagSize Ty.bool rfl (bagMap b2 Ty.bool rfl (.bin .gt (.var .here) (.int 1)))⟩),
    ("map into fewer slots keeps items", ⟨Ty.bool, bagContains Ty.bool rfl (bagMap b2 Ty.bool rfl (.bin .gt (.var .here) (.int 1))) tru⟩),
    ("values into more slots", ⟨Ty.bool, bagContains .str rfl (tableValues t2) (.str "c")⟩) ]

/-- Mapped items that outgrow the two slots of a bag of Bool. -/
def reslotOverflows : List (String × (t : Ty) × E t) :=
  [ ("map past the target's slots", ⟨.int, bagSize Ty.bool rfl (bagMap b3 Ty.bool rfl (.bin .gt (.var .here) (.int 1)))⟩) ]

/-- Expressions whose collections outgrow their one slot: the condition is false, so the script is unsat. -/
def overflows : List (String × (t : Ty) × E t) :=
  [ ("bag insert past the slots", ⟨.int, .call (.prim .bagSize [.int] rfl)
      (.cons (.call (.prim .bagInsert [.int] rfl) (.cons b3 (.cons (.int 7) .nil))) .nil)⟩),
    ("table insert past the slots", ⟨.int, tableSize (.call (.prim .tableInsert [.int, .str] rfl)
      (.cons t2 (.cons (.int 3) (.cons (.str "d") .nil))))⟩) ]

def dt : Script :=
  { datatypes := [Datatype.mk [[.int, .str], []], Datatype.mk [[.dt 0]]], vars := [.dt 1, .dt 0],
    asserts := [.eq (.var 0) (.ctor 1 0 [.ctor 0 0 [.int (-3), .str "x"]]), .eq (.var 1) (.ctor 0 1 [])],
    shows := [0, 1] }

/-- The script asking for a variable equal to the expression under its condition. Lists get their longest literal's
slots. -/
def scriptOf (slots : Ty → Nat) {t : Ty} (e : E t) : Except String (Layout × Script) := do
  let L := Layout.addTys (listSlots slots (Tazuna.Smt.Expr.lits e)) {} (Tazuna.Smt.Expr.tys e)
  match encode L (G := []) () e (), L.srt? t, L.datatypes? with
  | .ok (code, cond), some srt, some dts =>
    let some term := Code.term? t code | throw "no term"
    pure (L, { datatypes := dts, vars := [srt], asserts := [.eq (.var 0) term, cond], shows := [0] })
  | .error r, _, _ => throw s!"no encoding: {repr r}"
  | _, _, _ => throw "no sort"

/-- `fresh(source, index)`, with the source a variable the script fixes, as a step fixes its counter. -/
def freshOf (index : Int) : Expr [] [.dsl .fresh []] .id :=
  .call (.prim .fresh [] rfl) (.cons (.var .here) (.cons (.int index) .nil))

def freshScript (step : Nat) (index : Int) : Except String (Layout × Script) := do
  let L := Layout.addTys (fun _ => 3) {} [.id]
  match encode L (G := []) () (freshOf index) (Term.var 1, ()), L.srt? .id, L.datatypes? with
  | .ok (code, cond), some srt, some dts =>
    pure (L, { datatypes := dts, vars := [srt, .int], asserts := [.eq (.var 0) code, .eq (.var 1) (.int step), cond],
               shows := [0] })
  | .error r, _, _ => throw s!"no encoding: {repr r}"
  | _, _, _ => throw "no sort"

/-! A query step on a small service, for `step_encode`: the records are a table of Int to Int, the query `get` takes a
key from the caller "alice", accepts a positive key, and answers `table.get(ctx.records, key)`. Each case asks the
solver for a state and input whose outcome terms meet a goal, decodes them, runs `step` on what they decode to, and
compares its outcome with what the outcome terms denote in the model. Every code is the service's own: the encoding
of the source its structure value keeps (`QueryCode.of`, `EventCode.of`, `CommandCode.of`, `Fun.code`). -/

/-- What the layout builder reads of a kept function's source. -/
def funParts {t : Ty} (f : Fun t) : ProgramParts :=
  ⟨Tazuna.Ir.Expr.sites f.defs f.body, Tazuna.Ir.Expr.handles f.body, Tazuna.Smt.Expr.tys f.body,
    Tazuna.Smt.Expr.lits f.body⟩

def effParts {ps : List Ty} {r : Ty} (f : EffectFun ps r) : ProgramParts :=
  ⟨Tazuna.Ir.Expr.sites f.defs f.body, Tazuna.Ir.Expr.handles f.body, Tazuna.Smt.Expr.tys f.body,
    Tazuna.Smt.Expr.lits f.body⟩

def joinParts (ps : List ProgramParts) : ProgramParts :=
  ⟨ps.flatMap (·.sites), ps.flatMap (·.handles), ps.flatMap (·.tys), ps.flatMap (·.lits)⟩

/-- The sources of every function a service keeps, which stand for its program: a case has no loaded program. -/
def svcParts (v : ServiceV) : ProgramParts :=
  joinParts ([funParts v.apply, funParts v.invariants] ++ v.subscribes.map (funParts ·.wrap) ++
    v.commands.flatMap (fun c => [funParts c.accepts, funParts c.decide, funParts c.ensures]) ++
    v.queries.flatMap (fun q => [funParts q.accepts, funParts q.resolve]) ++
    v.machines.flatMap (fun m => [funParts m.instances, funParts m.on, funParts m.after, effParts m.effect,
      funParts m.invariants]) ++
    v.reactions.map (effParts ·.react))

/-- The layout `prove` builds for the service (`Layout.ofParts`), with `slots` for every bag and table; `extra` is
program code the case writes as terms rather than as the service's functions. -/
def svcLayout (v : ServiceV) (slots : Nat) (extra : ProgramParts := ⟨[], [], [], []⟩) : Layout :=
  Layout.ofParts (joinParts [svcParts v, extra]) { v with bounds := { v.bounds with items := slots } }

/-- A site as program code: the site, the type of every node of its source and its list literals. -/
def siteParts {Γ : List Ty} {t : Ty} (s : Site Γ t) : ProgramParts :=
  ⟨[⟨Γ, t, s⟩], Tazuna.Ir.Expr.handles s.body, Tazuna.Smt.Expr.tys s.body, Tazuna.Smt.Expr.lits s.body⟩

def recordsT : Ty := .table .int .int
def qctxT : Ty := Ty.queryCtx recordsT .int .str

/-- The pending table of a service without pending shapes: its state's layout holds it, and well-formedness keeps it
empty. -/
def noPending (v : ServiceV) : Ty := pendingTable ([] : List (PendingShape v.event))

/-- The symbolic state at `v0..v3` with the pending table at `vk`, for scripts whose `v4` holds an input. -/
def stateAt {v : ServiceV} (k : Nat) : SymState v := { SymState.vars 0 with pending := .var k }

/-- A step's terms through `encodeStep`, the encoding `step_encode` proves, for the input built at the layout's
pending table size. -/
def stepOf (L : Layout) (P : List AnySite) (v : ServiceV) (S : SymState v)
    (inp : (slots : Nat) → Except String (SymInput v (shapes v) slots)) : Except String (EncodedStep v) := do
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let senv ← enc (StepEnv.of L (shapes v))
  enc (encodeStep L prelude P v senv S (← inp senv.nT))

/-- The answer at the `k`-th pending shape and the `j`-th pending slot. -/
def answerAt {v : ServiceV} {shs : List (PendingShape v.event)} (k j : Nat) (to value : Term) (slots : Nat) :
    Except String (SymInput v shs slots) :=
  if hk : k < shs.length then
    if hj : j < slots then pure (.answer ⟨k, hk⟩ ⟨j, hj⟩ to value) else throw s!"no pending slot {j}"
  else throw s!"no pending shape {k}"

def acceptsE : E (.fn [.int] Ty.rules) :=
  .lam (.list (.cons (.tuple (.cons (.str "positive") (.cons (.bin .gt (.var .here) (.int 0)) .nil))) .nil))

def resolveE : E (.fn [qctxT] (Ty.option .int)) :=
  .lam (.call (.prim .tableGet [.int, .int] rfl)
    (.cons (.field (ft := recordsT) "records" 0 (by simp) (.var .here))
      (.cons (.field (ft := .int) "input" 1 (by simp) (.var .here)) .nil)))

def getQ : QueryV recordsT .str :=
  { name := "get", input := .int, output := Ty.option .int, callers := ["alice"],
    accepts := .closed acceptsE, resolve := .closed resolveE }

def querySvc : ServiceV :=
  { name := "s", records := recordsT, event := .int, caller := .str, init := Builtin.tableEmpty,
    apply := .closed (.lam (.var .here)), subscribes := [], declares := [], commands := [], queries := [getQ],
    sources := [],
    machines := [], reactions := [], invariants := .closed (.lam (.list .nil)), responses := [], bounds := ⟨[], 0, 0, 0⟩,
    scenarios := [], declared := [] }

def queryLayout : Layout :=
  Layout.addTys (listSlots (fun _ => 3) (Tazuna.Smt.Expr.lits acceptsE ++ Tazuna.Smt.Expr.lits resolveE)) {}
    (recordsT :: .id :: noPending querySvc :: Ty.option (.dsl .effect [querySvc.event]) :: Tazuna.Smt.Expr.tys acceptsE ++ Tazuna.Smt.Expr.tys resolveE)

/-- The script for one goal on the outcome terms: v0..v3 the state, v4 the caller, v5 the key, v6..v9 the outcome
terms (caller listed, the rule's holds and name, the output), v10 the pending table. -/
def queryScript (goal : List Term) : Except String (Script × QueryOut) := do
  let L := queryLayout
  let S := stateAt 10
  let t ← stepOf L [] querySvc S (fun _ => pure (.query ⟨0, by decide⟩ (.var 4) (.var 5)))
  let .query o := t.out | throw "not a query's terms"
  let some wf := S.wf L (v := querySvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some osrt := L.srt? (Ty.option .int) | throw "no output sort"
  let some psrt := L.srt? (noPending querySvc) | throw "no pending sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(name, holds)] := o.rules | throw "not one rule"
  pure ({ datatypes := dts, vars := [rsrt, .int, .int, .int, .str, .int, .bool, .bool, .str, osrt, psrt],
          asserts := [t.codes, t.sites, t.cond, wf,
            .eq (.var 6) o.callerOk, .eq (.var 7) holds, .eq (.var 8) name, .eq (.var 9) o.output] ++ goal,
          shows := List.range 11 }, o)

/-- Goals that only a state that does not decode meets: two occupied slots with one key, a negative counter. The
well-formedness makes each unsat, and each is sat without it. -/
def illFormed : List (String × Term) :=
  match queryLayout.find? recordsT, queryLayout.find? (.tuple [Ty.bool, .int, .int]) with
  | some (d, n), some (dt, _) =>
    let S := slotsOf d dt n 2 (.var 0)
    [("well-formedness excludes a repeated key",
        .and (.and S[0]!.1 S[1]!.1) (.eq (S[0]!.2[0]) (S[1]!.2[0]))),
     ("well-formedness excludes a negative counter", .lt (.var 2) (.int 0))]
  | _, _ => []

def illFormedScript (withWf : Bool) (goal : Term) : Except String Script := do
  let L := queryLayout
  let some wf := (SymState.vars 0).wf L (v := querySvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (noPending querySvc) | throw "no pending sort"
  let some dts := L.datatypes? | throw "no datatypes"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, psrt], asserts := (if withWf then [wf] else []) ++ [goal] }

/-- The model of the solver's values, as far as the variables go. -/
def modelOf (vs : List (Nat × Val)) : Model :=
  { vars := fun n => (vs.lookup n).getD default, divZero := fun _ => 0, modZero := fun _ => 0,
    selOther := fun _ _ _ _ => default, defs := fun _ => default }

/-- Runs one query case: the outcome `step` computes from the decoded state and input against the outcome terms. -/
def queryCase (solver : Solver) (name : String) (goal : List Term) : IO Bool := do
  match queryScript goal with
  | .error m => IO.println s!"smt-check: {name}: {m}"; return false
  | .ok (script, _) =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let L := queryLayout
      let o : QueryOut := ⟨.var 6, [(.var 8, .var 7)], .var 9⟩
      let i : Fin querySvc.queries.length := ⟨0, by decide⟩
      match (stateAt 10).decode M L (v := querySvc) prelude [],
          (SymInput.query (shs := []) (slots := 0) i (.var 4) (.var 5)).decode M L (v := querySvc) rfl with
      | some s, some x =>
        let r := step prelude querySvc s x
        let want := match o.invalid M with
          | some ns => Outcome.invalid ns |>.summary
          | none => "answered"
        let outOk := match r.outcome with
          | .answered ⟨t, y⟩ =>
            match Ty.same t (Ty.option .int) with
            | some ⟨h⟩ => (embedV L _ (Ty.up _ rfl (h ▸ y))).map (·.print) ==
                (((vs.lookup 9).bind (decodeV L (Ty.option .int))).bind (embedV L _)).map (·.print)
            | none => false
          | _ => true
        if r.outcome.summary != want || !outOk then
          IO.println s!"smt-check: {name}: step says {r.outcome.summary}, the terms say {want}"; return false
        return true
      | _, _ => IO.println s!"smt-check: {name}: the model does not decode"; return false
    | a => IO.println s!"smt-check: {name}: {repr a}"; return false

def queryCases : List (String × List Term) :=
  let some_ (t : Term) : Term := match queryLayout.find? (Ty.option .int) with
    | some (d, _) => .is d 0 t
    | none => .bool false
  [ ("query answers a key the records hold", [.var 6, .var 7, some_ (.var 9)]),
    ("query answers a key the records lack", [.var 6, .var 7, .not (some_ (.var 9))]),
    ("query refuses an unlisted caller", [.not (.var 6)]),
    ("query refuses a key that is not positive", [.var 6, .not (.var 7)]) ]

/-! An event step on a service without machines or reactions, for `step_encode`: the subscription's value is a key
and a value, the records insert it, and the invariant `small` holds while the table has fewer than three keys. -/

def evT : Ty := .tuple [.int, .int]

def wrapE : E (.fn [evT] evT) := .lam (.var .here)

def applyE : E (.fn [recordsT, evT] recordsT) :=
  .lam (.call (.prim .tableInsert [.int, .int] rfl)
    (.cons (.var .here) (.cons (.index (ts := [.int, .int]) (.var (.there .here)) ⟨0, by decide⟩)
      (.cons (.index (ts := [.int, .int]) (.var (.there .here)) ⟨1, by decide⟩) .nil))))

def invariantsE : E (.fn [recordsT] Ty.rules) :=
  .lam (.list (.cons (.tuple (.cons (.str "small")
    (.cons (.bin .lt (.call (.prim .tableSize [.int, .int] rfl) (.cons (.var .here) .nil)) (.int 3)) .nil))) .nil))

def eventSvc : ServiceV :=
  { name := "e", records := recordsT, event := evT, caller := .str, init := Builtin.tableEmpty,
    apply := .closed applyE,
    subscribes := [⟨"x", "set", evT, .closed wrapE⟩], declares := [], commands := [],
    queries := [], sources := [], machines := [], reactions := [],
    invariants := .closed invariantsE, responses := [], bounds := ⟨[], 0, 0, 0⟩,
    scenarios := [], declared := [] }

def eventLayout : Layout :=
  Layout.addTys (listSlots (fun _ => 3) (Tazuna.Smt.Expr.lits applyE ++ Tazuna.Smt.Expr.lits invariantsE)) {}
    (recordsT :: evT :: noPending eventSvc :: Ty.option (.dsl .effect [evT]) :: Tazuna.Smt.Expr.tys applyE ++
      Tazuna.Smt.Expr.tys invariantsE)

def eventI : Fin eventSvc.subscribes.length := ⟨0, by decide⟩

/-- An event step's terms through `encodeStep`. -/
def eventTerms (L : Layout) (P : List AnySite) (v : ServiceV) (i : Fin v.subscribes.length) (S : SymState v)
    (value : Term) : Except String (EventOut v × EncodedStep v) := do
  let t ← stepOf L P v S (fun _ => pure (.event i value))
  let .event o := t.out | throw "not an event's terms"
  pure (o, t)

/-- v0..v3 the state, v4 the value, v5 the records after, v6 the event, v7 and v8 the invariant's holds and name, v9
the pending table. -/
def eventScript (goal : List Term) : Except String Script := do
  let L := eventLayout
  let S := stateAt 9
  let (o, t) ← eventTerms L [] eventSvc eventI S (.var 4)
  let some wf := S.wf L (v := eventSvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some esrt := L.srt? evT | throw "no event sort"
  let some psrt := L.srt? (noPending eventSvc) | throw "no pending sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(name, holds)] := o.finish.invariants | throw "not one invariant"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, esrt, rsrt, esrt, .bool, .str, psrt],
         asserts := [t.codes, t.sites, t.cond, wf, .eq (.var 5) o.finish.settle.terms.done.records, .eq (.var 6) o.event,
           .eq (.var 7) holds, .eq (.var 8) name] ++ goal,
         shows := List.range 10 }

/-- Whether the model's value decodes to a value `==` to `x`. -/
def sameAs (L : Layout) (t : Ty) (h : t.isData = true) (x : t.den0) (w : Option Val) : Bool :=
  match w.bind (decodeV L t) with
  | some y => (Ty.semWith Dsl.val t).2 (Ty.up t h x) y
  | none => false

def eventCase (solver : Solver) (name : String) (goal : List Term) : IO Bool := do
  match eventScript goal with
  | .error m => IO.println s!"smt-check: {name}: {m}"; return false
  | .ok script =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let L := eventLayout
      match (stateAt 9).decode M L (v := eventSvc) prelude [],
          (SymInput.event (shs := []) (slots := 0) eventI (.var 4)).decode M L (v := eventSvc) rfl with
      | some s, some x =>
        let r := step prelude eventSvc s x
        let ok := match brokenIn M [(.var 8, .var 7)], r.outcome, r.events with
          | n :: _, .fault (.invariant n'), [] => n == n' && sameAs L recordsT rfl r.state.records (vs.lookup 0)
          | [], .accepted, [e] => sameAs L recordsT rfl r.state.records (vs.lookup 5) && sameAs L evT rfl e (vs.lookup 6)
          | _, _, _ => false
        unless ok do IO.println s!"smt-check: {name}: step says {r.outcome.summary}, the terms differ"
        return ok
      | _, _ => IO.println s!"smt-check: {name}: the model does not decode"; return false
    | a => IO.println s!"smt-check: {name}: {repr a}"; return false

def eventCases : List (String × List Term) :=
  [ ("event keeps the invariant", [.var 7]),
    ("event breaks the invariant", [.not (.var 7)]) ]

/-! The whole event step with a machine and no pending shape, for `step_encode`: the event service above with a
machine `calm` whose instances are the records' keys; an instance in state 0 enters 1 on any event, and its invariant
`calm` holds below state 1. The decoded state and input step (`step`) to the outcome the terms give: the first broken
name (the service's, then the instances' in key order) as the fault, else the records, the event, the new instance
table, an empty pending table and the same next id. Where an instance breaks `calm`, the step of the same state
without the machine must not pass the comparison. -/

def intDen : (t : Ty) → t.den0 → Option Int
  | .int, x => some x
  | _, _ => none

def evCtxT : Ty := Ty.machineCtx .int .int recordsT

def evOnE : Expr [] [] (.fn [evCtxT, evT] (Ty.next .int)) :=
  let st : Expr [] [evCtxT, evT] .int := .field (ft := .int) "state" 1 (by simp) (.var .here)
  .lam (.case (.bin (.eq rfl) st (.int 0))
    (.cons (.ctor (vs := [[], []]) ⟨0, by decide⟩ .nil) (.ctor (vs := [[], [.int]]) ⟨1, by decide⟩ (.cons (.int 1) .nil))
      (.cons (.ctor (vs := [[], []]) ⟨1, by decide⟩ .nil) (.ctor (vs := [[], [.int]]) ⟨0, by decide⟩ .nil) .nil)) ⟨4, rfl⟩)

def evInvE : Expr [] [] (.fn [evCtxT] Ty.rules) :=
  let st : Expr [] [evCtxT] .int := .field (ft := .int) "state" 1 (by simp) (.var .here)
  .lam (.list (.cons (.tuple (.cons (.str "calm") (.cons (.bin .lt st (.int 1)) .nil))) .nil))

def evM : MachineV recordsT evT :=
  { name := "calm", key := .int, state := .int,
    instances := .closed (.lam (.call (.prim .tableKeys [.int, .int] rfl) (.cons (.var .here) .nil))),
    initial := (0 : Int), on := .closed evOnE,
    after := .closed (.lam (.ctor (vs := [[Ty.timer .int], []]) ⟨1, by decide⟩ .nil)),
    effect := .closed (.lam (.ctor (vs := [[Ty.dsl .effect [evT]], []]) ⟨1, by decide⟩ .nil)),
    invariants := .closed evInvE }

def evMSvc : ServiceV := { eventSvc with name := "em", machines := [evM] }

def evMLayout : Layout :=
  Layout.addTys (listSlots (fun _ => 3)
      (Tazuna.Smt.Expr.lits applyE ++ Tazuna.Smt.Expr.lits invariantsE ++ Tazuna.Smt.Expr.lits evInvE)) {}
    ([recordsT, evT, evM.table, .bag .int, evCtxT, Ty.next .int, Ty.option (Ty.timer .int), Ty.timer .int,
      Ty.option (.tuple [.int, .int]), .tuple [.int, .int], instEntry .int, Ty.option (.dsl .effect [evT]),
      noPending evMSvc, .tuple [.int]] ++
      Tazuna.Smt.Expr.tys applyE ++ Tazuna.Smt.Expr.tys invariantsE ++ Tazuna.Smt.Expr.tys evOnE ++
      Tazuna.Smt.Expr.tys evInvE)

def evMI : Fin evMSvc.subscribes.length := ⟨0, by decide⟩

/-- v0..v3 the state, v4 the pending table, v5 the instance table, v6 the value, v7 the records after, v8 the event,
v9 and v10 the service invariant's holds and name, v11 the new instance table, v12 the new pending table, v13 the
next id after. -/
def evMScript (goal : List InstCheck → List Term) :
    Except String (Script × PerMachine (fun _ => List InstCheck) evMSvc.machines) := do
  let L := evMLayout
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let shs : List (PendingShape evMSvc.event) := []
  let (o, t) ← eventTerms L [] evMSvc evMI S (.var 6)
  let d := o.finish.settle.terms.done
  let checks := o.finish.checks
  let below ← enc (pendingBelowT L shs S.pending S.nextId)
  let some wf := S.wf L (v := evMSvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some esrt := L.srt? evT | throw "no event sort"
  let some msrt := L.srt? evM.table | throw "no table sort"
  let some psrt := L.srt? (noPending evMSvc) | throw "no pending sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(name, holds)] := o.finish.invariants | throw "not one invariant"
  let [tbl] := d.tables.toList | throw "not one machine"
  let [cs] := checks.toList | throw "not one machine"
  pure ({ datatypes := dts,
          vars := [rsrt, .int, .int, .int, psrt, msrt, esrt, rsrt, esrt, .bool, .str, msrt, psrt, .int],
          asserts := [t.codes, t.sites, t.cond, wf, below, .eq (.var 7) d.records, .eq (.var 8) o.event,
            .eq (.var 9) holds, .eq (.var 10) name, .eq (.var 11) tbl, .eq (.var 12) o.finish.pending,
            .eq (.var 13) d.nextId] ++ goal cs,
          shows := List.range 14 }, checks)

def evMCase (solver : Solver) (name : String) (goal : List InstCheck → List Term) (machineFault : Bool) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: {name}: {m}"; return false
  match evMScript goal with
  | .error m => fail m
  | .ok (script, checks) =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let L := evMLayout
      match (SymState.vars 0).decode M L (v := evMSvc) prelude [],
          (SymInput.event (shs := []) (slots := 0) evMI (.var 6)).decode M L (v := evMSvc) rfl with
      | some s, some x =>
        let names := brokenIn M [(.var 10, .var 9)] ++ checksBroken L prelude M evMSvc.machines checks
        let view (sms : List (Step.MachineState recordsT evT)) := sms.flatMap fun ⟨_, is⟩ => is.map fun i =>
          (intDen _ i.key, intDen _ i.state)
        let newInsts := match decodeV L evM.table ((Term.var 11).denote M) with
          | some tbl => some (view [⟨evM, instancesOf prelude evM (Ty.down _ evM.table_data tbl)⟩])
          | none => none
        let agrees (outcome : Outcome) (records : recordsT.den0) (events : List evT.den0)
            (machines : List (Step.MachineState recordsT evT)) : Bool :=
          match names, outcome, events with
          | n :: _, .fault (.invariant n'), [] => n == n' && sameAs L recordsT rfl records (vs.lookup 0)
          | [], .accepted, [e] => sameAs L recordsT rfl records (vs.lookup 7) && sameAs L evT rfl e (vs.lookup 8) &&
              newInsts == some (view machines)
          | _, _, _ => false
        let r := step prelude evMSvc s x
        let pendingOk := match decodePending L ([] : List (PendingShape evMSvc.event)) ((Term.var 12).denote M),
            vs.lookup 13 with
          | some [], some (.int n) => n == s.nextId && r.state.pending.isEmpty && r.state.nextId == s.nextId
          | _, _ => false
        let mut ok := true
        if !agrees r.outcome r.state.records r.events r.state.machines.toSigma then
          ok ← fail s!"step says {r.outcome.summary}, the terms give {names}"
        if names.isEmpty && !pendingOk then ok ← fail "the pending table or next id differs from the step's"
        if machineFault && names.isEmpty then ok ← fail "no instance breaks its invariant"
        if machineFault then
          let s0 : State eventSvc :=
            { records := s.records, machines := .nil, pending := [], now := s.now, fresh := s.fresh, nextId := s.nextId }
          let x0 : Input eventSvc := match x with
            | .event ⟨0, _⟩ value => .event eventI value
            | _ => .clock 0
          let r0 := step prelude eventSvc s0 x0
          if agrees r0.outcome r0.state.records r0.events [] then
            ok ← fail "the step without the machine passes the comparison"
        return ok
      | _, _ => fail "the model does not decode"
    | a => fail s!"{repr a}"

/-- A goal that steers the model: every occupied instance keeps its invariants. -/
def instancesKeep (checks : List InstCheck) : Term :=
  allT (checks.map fun c => .or (.not c.occupied) (allT (c.rules.map (·.2))))

def evMCases : List (String × (List InstCheck → List Term) × Bool) :=
  [ ("event with a machine keeps the invariants", (fun cs => [.var 9, instancesKeep cs]), false),
    ("event with a machine breaks an instance invariant", (fun cs => [.var 9, .not (instancesKeep cs)]), true),
    ("event with a machine breaks the service invariant", (fun _ => [.not (.var 9)]), false) ]

/-- A clock line on the event service, which has no machine and no pending shape, for `step_encode`: v0..v3 the state,
v4 the line's time, v5 whether time moves forward, v6 and v7 the invariant's holds and name, v8 whether every round
fired, v9 the pending table, v10 the new pending table, v11 the next id after. -/
def clockScript (goal : List Term) : Except String Script := do
  let L := eventLayout
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let shs : List (PendingShape eventSvc.event) := []
  let S := stateAt 9
  let t ← stepOf L [] eventSvc S (fun _ => pure (.clock (.var 4)))
  let .clock o := t.out | throw "not a clock line's terms"
  let below ← enc (pendingBelowT L shs S.pending S.nextId)
  let some wf := S.wf L (v := eventSvc) shs | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (noPending eventSvc) | throw "no pending sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(name, holds)] := o.finish.invariants | throw "not one invariant"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, .int, .bool, .bool, .str, .bool, psrt, psrt, .int],
         asserts := [t.codes, t.sites, t.cond, wf, below, .eq (.var 5) o.forward, .eq (.var 6) holds, .eq (.var 7) name,
           .eq (.var 8) o.over, .eq (.var 10) o.finish.pending, .eq (.var 11) o.finish.settle.terms.done.nextId] ++ goal,
         shows := List.range 12 }

def clockCase (solver : Solver) (name : String) (goal : List Term) : IO Bool := do
  match clockScript goal with
  | .error m => IO.println s!"smt-check: {name}: {m}"; return false
  | .ok script =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let L := eventLayout
      match (stateAt 9).decode M L (v := eventSvc) prelude [],
          (SymInput.clock (shs := []) (slots := 0) (.var 4)).decode M L (v := eventSvc) rfl,
          decodePending L ([] : List (PendingShape eventSvc.event)) ((Term.var 10).denote M), vs.lookup 11 with
      | some s, some x@(.clock time), some pend', some (.int n') =>
        let r := step prelude eventSvc s x
        let ok := match (M.vars 5).toBool, (M.vars 8).toBool, brokenIn M [(.var 7, .var 6)], r.outcome with
          | false, _, _, .invalid ["time moves forward"] => r.state.now == s.now
          | true, false, n :: _, .fault (.invariant n') => n == n' && r.state.now == s.now
          | true, false, [], .accepted => r.state.now == time && sameAs L recordsT rfl r.state.records (vs.lookup 0) &&
              pend'.isEmpty && r.state.pending.isEmpty && n' == r.state.nextId
          | _, _, _, _ => false
        unless ok do IO.println s!"smt-check: {name}: step says {r.outcome.summary}, the terms differ"
        return ok
      | _, _, _, _ => IO.println s!"smt-check: {name}: the model does not decode"; return false
    | a => IO.println s!"smt-check: {name}: {repr a}"; return false

def clockCases : List (String × List Term) :=
  [ ("clock moves time on", [.var 5, .var 6, .lt (.var 1) (.var 4)]),
    ("clock reports a broken invariant", [.var 5, .not (.var 6)]),
    ("clock refuses an earlier time", [.not (.var 5)]) ]

/-! A command step on the event service, for `step_encode`: `put` takes a key from the caller "alice", accepts a
positive key, rejects a key above 10, accepts 7 with no events and any other key with two events that insert it and
the next key; it ensures the records grew, and the invariant `small` holds below three keys. -/

def cctxT : Ty := Ty.ctx recordsT .int .str

def inputOf : Expr [] [cctxT] .int := .field (ft := .int) "input" 1 (by simp) (.var .here)

def boolCase {Γ : List Ty} {r : Ty} (c : Expr [] Γ Ty.bool) (yes no : Expr [] Γ r) : Expr [] Γ r :=
  .case c (.cons (.ctor (vs := [[], []]) ⟨0, by decide⟩ .nil) yes
    (.cons (.ctor (vs := [[], []]) ⟨1, by decide⟩ .nil) no .nil)) ⟨10, rfl⟩

def decideE : E (.fn [cctxT] (Ty.result (.list evT) .str)) :=
  let pair (k : Expr [] [cctxT] .int) (v : Int) : Expr [] [cctxT] evT := .tuple (.cons k (.cons (.int v) .nil))
  .lam (boolCase (.bin .gt inputOf (.int 10))
    (.ctor (vs := [[.list evT], [.str]]) ⟨1, by decide⟩ (.cons (.str "big") .nil))
    (boolCase (.bin (.eq rfl) inputOf (.int 7))
      (.ctor (vs := [[.list evT], [.str]]) ⟨0, by decide⟩ (.cons (.list .nil) .nil))
      (.ctor (vs := [[.list evT], [.str]]) ⟨0, by decide⟩
        (.cons (.list (.cons (pair inputOf 1) (.cons (pair (.bin .add inputOf (.int 1)) 2) .nil))) .nil))))

def ensuresE : E (.fn [cctxT, recordsT] Ty.rules) :=
  let size {Γ : List Ty} (t : Expr [] Γ recordsT) : Expr [] Γ .int :=
    .call (.prim .tableSize [.int, .int] rfl) (.cons t .nil)
  .lam (.list (.cons (.tuple (.cons (.str "grows")
    (.cons (.bin .gt (size (.var (.there .here))) (size (.field (ft := recordsT) "records" 0 (by simp) (.var .here))))
      .nil))) .nil))

def putC : CommandV recordsT evT .str :=
  { name := "put", input := .int, rejection := .str, callers := ["alice"],
    accepts := .closed acceptsE, decide := .closed decideE,
    ensures := .closed ensuresE }

def commandSvc : ServiceV := { eventSvc with name := "c", commands := [putC] }

def commandLayout : Layout :=
  let lits := Tazuna.Smt.Expr.lits acceptsE ++ Tazuna.Smt.Expr.lits decideE ++ Tazuna.Smt.Expr.lits ensuresE ++
    Tazuna.Smt.Expr.lits applyE ++ Tazuna.Smt.Expr.lits invariantsE
  Layout.addTys (listSlots (fun _ => 3) lits) {} (recordsT :: evT :: .id :: noPending commandSvc :: Ty.option (.dsl .effect [evT]) ::
    Tazuna.Smt.Expr.tys acceptsE ++
    Tazuna.Smt.Expr.tys decideE ++ Tazuna.Smt.Expr.tys ensuresE ++ Tazuna.Smt.Expr.tys applyE ++
    Tazuna.Smt.Expr.tys invariantsE)

/-- v0..v3 the state, v4 the caller, v5 the key, then the outcome terms: v6 caller listed, v7 and v8 the `accepts`
rule, v9 accepted by `decide`, v10 the rejection, v11 the events, v12 and v13 the `ensures` rule, v14 the records
after, v15 and v16 the invariant, v17 the pending table. -/
def commandScript (goal : List Term) : Except String Script := do
  let L := commandLayout
  let S := stateAt 17
  let t ← stepOf L [] commandSvc S (fun _ => pure (.command ⟨0, by decide⟩ (.var 4) (.var 5)))
  let .command o := t.out | throw "not a command's terms"
  let some wf := S.wf L (v := commandSvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some lsrt := L.srt? (.list evT) | throw "no events sort"
  let some psrt := L.srt? (noPending commandSvc) | throw "no pending sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(an, ah)] := o.rules | throw "not one rule"
  let [(en, eh)] := o.decided.ensures | throw "not one ensures rule"
  let [(iname, ih)] := o.finish.invariants | throw "not one invariant"
  pure { datatypes := dts,
         vars := [rsrt, .int, .int, .int, .str, .int, .bool, .bool, .str, .bool, .str, lsrt, .bool, .str, rsrt, .bool,
           .str, psrt],
         asserts := [t.codes, t.sites, t.cond, wf, .eq (.var 6) o.callerOk, .eq (.var 7) ah, .eq (.var 8) an, .eq (.var 9) o.decided.ok,
           .eq (.var 10) o.decided.rejection, .eq (.var 11) o.decided.events, .eq (.var 12) eh, .eq (.var 13) en,
           .eq (.var 14) o.decided.after.records, .eq (.var 15) ih, .eq (.var 16) iname] ++ goal,
         shows := List.range 18 }

def commandCase (solver : Solver) (name : String) (goal : List Term) : IO Bool := do
  match commandScript goal with
  | .error m => IO.println s!"smt-check: {name}: {m}"; return false
  | .ok script =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let L := commandLayout
      let i : Fin commandSvc.commands.length := ⟨0, by decide⟩
      match (stateAt 17).decode M L (v := commandSvc) prelude [],
          (SymInput.command (shs := []) (slots := 0) i (.var 4) (.var 5)).decode M L (v := commandSvc) rfl with
      | some s, some x =>
        let r := step prelude commandSvc s x
        let one (n h : Nat) := brokenIn M [(.var n, .var h)]
        let ok := r.state.fresh == s.fresh + 1 && match (M.vars 6).toBool, one 8 7, (M.vars 9).toBool, one 13 12,
            one 16 15, r.outcome with
          | false, _, _, _, _, .invalid ["callers"] => true
          | true, n :: ns, _, _, _, .invalid ms => n :: ns == ms
          | true, [], false, _, _, .rejected ⟨t, j⟩ =>
            match Ty.same t .str with
            | some ⟨h⟩ => sameAs L .str rfl (h ▸ j) (vs.lookup 10)
            | none => false
          | true, [], true, n :: _, _, .fault (.ensures n') => n == n'
          | true, [], true, [], n :: _, .fault (.invariant n') => n == n'
          | true, [], true, [], [], .accepted => sameAs L recordsT rfl r.state.records (vs.lookup 14) &&
            sameAs L (.list evT) rfl r.events (vs.lookup 11)
          | _, _, _, _, _, _ => false
        unless ok do IO.println s!"smt-check: {name}: step says {r.outcome.summary}, the terms differ"
        return ok
      | _, _ => IO.println s!"smt-check: {name}: the model does not decode"; return false
    | a => IO.println s!"smt-check: {name}: {repr a}"; return false

def commandCases : List (String × List Term) :=
  [ ("command accepts a key", [.var 6, .var 7, .var 9, .var 12, .var 15]),
    ("command rejects a big key", [.var 6, .var 7, .not (.var 9)]),
    ("command refuses an unlisted caller", [.not (.var 6)]),
    ("command refuses a key that is not positive", [.var 6, .not (.var 7)]),
    ("command breaks its ensures", [.var 6, .var 7, .var 9, .not (.var 12)]),
    ("command breaks the invariant", [.var 6, .var 7, .var 9, .var 12, .not (.var 15)]) ]

/-! Pending requests as a symbolic table, for `decode_state`: a service whose reaction may ask the external `fx` to
`pay` (a command) or for a `rate` (a query). Each `on_answer` site captures an Int, so the service has two pending
shapes, and a model's table decodes to requests whose `on_answer` is the site's closure record at the captured
value. -/

def payAnswerE : Expr [] [.int] (.fn [Ty.result .int .str] (.list .int)) := .lam (.list (.cons (.var (.there .here)) .nil))

def rateAnswerE : Expr [] [.int] (.fn [.int] (.list .int)) :=
  .lam (.list (.cons (.bin .add (.var .here) (.var (.there .here))) .nil))

def rateEnsuresE : Expr [] [] (.fn [.str, .int] Ty.rules) :=
  .lam (.list (.cons (.tuple (.cons (.str "positive") (.cons (.bin .lt (.int 0) (.var (.there .here))) .nil))) .nil))

def insertE : E (.fn [recordsT, .int] recordsT) :=
  .lam (.call (.prim .tableInsert [.int, .int] rfl)
    (.cons (.var .here) (.cons (.var (.there .here)) (.cons (.var (.there .here)) .nil))))

def pendingSites : List AnySite :=
  [⟨[.int], _, ⟨⟨"m", 1, 1, 0⟩, [], .nil, rfl, rfl, payAnswerE⟩⟩, ⟨[.int], _, ⟨⟨"m", 2, 1, 0⟩, [], .nil, rfl, rfl, rateAnswerE⟩⟩,
   ⟨[], _, ⟨⟨"m", 3, 1, 0⟩, [], .nil, rfl, rfl, rateEnsuresE⟩⟩]

/-- The reaction's source writes the three sites, so its requests can hold them (`senderShapes`); it starts none. -/
def askR : ReactionV recordsT .int := ⟨"ask", .closed (.lam
  (.let_ (.close ⟨"m", 1, 1, 0⟩ (.cons (.int 0) .nil) rfl rfl payAnswerE)
  (.let_ (.close ⟨"m", 2, 1, 0⟩ (.cons (.int 0) .nil) rfl rfl rateAnswerE)
  (.let_ (.close ⟨"m", 3, 1, 0⟩ .nil rfl rfl rateEnsuresE) (.list .nil)))))⟩

def fxDeclared : List (String × DeclaredV) :=
  [("fx", .externalCommand "pay" .str .int .str), ("fx", .externalQuery "rate" .str .int (.closed rateEnsuresE))]

def insertSvc : ServiceV := { querySvc with apply := .closed insertE, invariants := .closed invariantsE }

def pendingSvc : ServiceV := { insertSvc with name := "p", queries := [], reactions := [askR], declared := fxDeclared }

def pendingShapes : List (PendingShape pendingSvc.event) := shapes pendingSvc

def pendingLayout : Layout :=
  let lits := Tazuna.Smt.Expr.lits insertE ++ Tazuna.Smt.Expr.lits invariantsE ++ Tazuna.Smt.Expr.lits payAnswerE ++
    Tazuna.Smt.Expr.lits rateAnswerE ++ Tazuna.Smt.Expr.lits rateEnsuresE
  Layout.addTys (listSlots (fun _ => 3) lits) {} (recordsT :: pendingTable pendingShapes :: .list .int :: .tuple [] ::
    Ty.reactionCtx recordsT :: .list (.dsl .effect [.int]) :: Ty.option (.dsl .effect [.int]) ::
    Tazuna.Smt.Expr.tys insertE ++ Tazuna.Smt.Expr.tys invariantsE ++ Tazuna.Smt.Expr.tys payAnswerE ++
    Tazuna.Smt.Expr.tys rateAnswerE ++ Tazuna.Smt.Expr.tys rateEnsuresE)

/-- The pending table's slots in v4, and the entry datatype. -/
def pendingSlots : Option (List (Slot 2) × Nat) :=
  match pendingLayout.find? (pendingTable pendingShapes),
      pendingLayout.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry pendingShapes]),
      pendingLayout.find? (pendingEntry pendingShapes) with
  | some (d, n), some (dt, _), some (de, _) => some (slotsOf d dt n 2 (.var 4), de)
  | _, _, _ => none

def pendingScript (withWf : Bool) (goal : List Term) : Except String Script := do
  let L := pendingLayout
  let some wf := (SymState.vars 0).wf L (v := pendingSvc) pendingShapes | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable pendingShapes) | throw "no pending sort"
  let some dts := L.datatypes? | throw "no datatypes"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, psrt], asserts := (if withWf then [wf] else []) ++ goal,
         shows := List.range 5 }

/-- Goals on the pending table: slot 0 holds a `rate` request with wire id 3 whose `on_answer` captured 7, and slot 1
another request; with a repeated wire id or a negative one the well-formedness makes the goal unsat. -/
def pendingGoals : Option (List Term × List (String × Term)) := do
  let (S, de) ← pendingSlots
  let id (j : Nat) := (S[j]!.2[0])
  let entry (j : Nat) := (S[j]!.2[1])
  let rate := Term.and (.is de 1 (entry 0)) (.eq (.sel 1000 0 0 (.sel de 1 3 (entry 0))) (.int 7))
  pure ([S[0]!.1, S[1]!.1, .eq (id 0) (.int 3), rate],
    [("well-formedness excludes a repeated wire id", .and (.and S[0]!.1 S[1]!.1) (.eq (id 0) (id 1))),
     ("well-formedness excludes a negative wire id", .and S[0]!.1 (.lt (id 0) (.int 0)))])

def pendingCheck (solver : Solver) : IO Bool := do
  let some (goal, illFormed) := pendingGoals | IO.println "smt-check: pending: no layout"; return false
  let mut ok := true
  if pendingShapes.length != 2 then IO.println "smt-check: pending: not two shapes"; ok := false
  -- The captured value sits in the tuple of the site's captures; its datatype is the layout's.
  let some (dc, _) := pendingLayout.find? (.tuple [.int]) | IO.println "smt-check: pending: no capture tuple"; return false
  let goal := goal.map fun t => match t with
    | .and a (.eq (.sel _ 0 0 x) n) => .and a (.eq (.sel dc 0 0 x) n)
    | t => t
  match pendingScript true goal with
  | .error m => IO.println s!"smt-check: pending: {m}"; ok := false
  | .ok script =>
    match ← solver.run script with
    | .sat vs =>
      match (SymState.vars 0).decode (modelOf vs) pendingLayout (v := pendingSvc) prelude pendingShapes with
      | some s =>
        -- The decoded request runs the site's source at the captured value: answering 5 yields [5 + 7].
        let rate := s.pending.find? (·.id == 3)
        let answered := rate.bind fun p => match Ty.same (answerTy p.request.output p.request.rejection) .int with
          | some ⟨h⟩ => some (show List Int from p.request.onAnswer.fn (h ▸ (5 : Int), ()))
          | none => none
        if s.pending.length != 2 || rate.map (·.request.name) != some "rate" || answered != some [12] then
          IO.println "smt-check: pending: the decoded requests differ from the model"; ok := false
      | none => IO.println "smt-check: pending: the model does not decode"; ok := false
    | a => IO.println s!"smt-check: pending: {repr a}"; ok := false
  for (name, g) in illFormed do
    for (withWf, want) in [(true, "unsat"), (false, "sat")] do
      match pendingScript withWf [g] with
      | .ok script =>
        let got := match ← solver.run script with
          | .unsat => "unsat"
          | .sat _ => "sat"
          | _ => "unknown"
        if got != want then IO.println s!"smt-check: {name} (well-formedness {withWf}): {got}"; ok := false
      | .error m => IO.println s!"smt-check: {name}: {m}"; ok := false
  return ok

/-! A machine's instances as a symbolic table, for `decode_state` and `wf_decode`: one machine keyed by Int with Int
states. A model's table decodes to instances in key order, whatever slots hold them, and a key twice is not
well-formed. -/

def doorM : MachineV recordsT .int :=
  { name := "door", key := .int, state := .int, instances := .closed (.lam (.call (.prim .tableKeys [.int, .int] rfl)
      (.cons (.var .here) .nil))), initial := (0 : Int), on := .closed (.lam (.ctor (vs := [[], [.int]]) ⟨0, by decide⟩ .nil)),
    after := .closed (.lam (.ctor (vs := [[Ty.timer .int], []]) ⟨1, by decide⟩ .nil)), effect := .closed (.lam (.ctor (vs := [[Ty.dsl .effect [.int]], []]) ⟨1, by decide⟩ .nil)),
    invariants := .closed (.lam (.list .nil)) }

def doorSvc : ServiceV := { querySvc with name := "d", queries := [], machines := [doorM] }

def doorLayout : Layout := Layout.addTys (fun _ => 3) {} [recordsT, doorM.table, noPending doorSvc]

def doorScript (withWf : Bool) (goal : List Term) : Except String Script := do
  let L := doorLayout
  let some wf := (SymState.vars 0).wf L (v := doorSvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some msrt := L.srt? doorM.table | throw "no instance table sort"
  let some psrt := L.srt? (noPending doorSvc) | throw "no pending sort"
  let some dts := L.datatypes? | throw "no datatypes"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt], asserts := (if withWf then [wf] else []) ++ goal,
         shows := List.range 6 }

/-- Goals on the instance table in v5: slot 0 holds key 3 in state 1 with a timer due at 10 for state 2, slot 1 key 1
in state 0 with no timer; with one key in two slots the well-formedness makes the goal unsat. -/
def doorGoals : Option (List Term × List (String × Term)) := do
  let (d, n) ← doorLayout.find? doorM.table
  let (dt, _) ← doorLayout.find? (.tuple [Ty.bool, .int, instEntry .int])
  let (de, _) ← doorLayout.find? (instEntry .int)
  let (dopt, _) ← doorLayout.find? (Ty.option (.tuple [.int, .int]))
  let (dtm, _) ← doorLayout.find? (.tuple [.int, .int])
  let S := slotsOf d dt n 2 (.var 5)
  let key (j : Nat) := S[j]!.2[0]
  let entry (j : Nat) := S[j]!.2[1]
  let timer (j : Nat) := Term.sel de 0 1 (entry j)
  pure ([S[0]!.1, S[1]!.1, .not S[2]!.1, .eq (key 0) (.int 3), .eq (.sel de 0 0 (entry 0)) (.int 1),
      .is dopt 0 (timer 0), .eq (.sel dtm 0 0 (.sel dopt 0 0 (timer 0))) (.int 10),
      .eq (.sel dtm 0 1 (.sel dopt 0 0 (timer 0))) (.int 2),
      .eq (key 1) (.int 1), .eq (.sel de 0 0 (entry 1)) (.int 0), .is dopt 1 (timer 1)],
    [("well-formedness excludes an instance key twice", .and (.and S[0]!.1 S[1]!.1) (.eq (key 0) (key 1)))])

def doorCheck (solver : Solver) : IO Bool := do
  let some (goal, illFormed) := doorGoals | IO.println "smt-check: instances: no layout"; return false
  let mut ok := true
  match doorScript true goal with
  | .error m => IO.println s!"smt-check: instances: {m}"; ok := false
  | .ok script =>
    match ← solver.run script with
    | .sat vs =>
      match (SymState.vars 0).decode (modelOf vs) doorLayout (v := doorSvc) prelude [] with
      | some s =>
        -- Slot 0 holds key 3 and slot 1 key 1, yet the instances come in key order.
        let insts := s.machines.toSigma.map fun ⟨_, is⟩ => is.map fun i =>
          (intDen _ i.key, intDen _ i.state, i.timer.map fun (d, st) => (d, intDen _ st))
        if insts != [[(some 1, some 0, none), (some 3, some 1, some (10, some 2))]] then
          IO.println s!"smt-check: instances: the decoded instances differ from the model: {insts}"; ok := false
      | none => IO.println "smt-check: instances: the model does not decode"; ok := false
    | a => IO.println s!"smt-check: instances: {repr a}"; ok := false
  for (name, g) in illFormed do
    for (withWf, want) in [(true, "unsat"), (false, "sat")] do
      match doorScript withWf [g] with
      | .ok script =>
        let got := match ← solver.run script with
          | .unsat => "unsat"
          | .sat _ => "sat"
          | _ => "unknown"
        if got != want then IO.println s!"smt-check: {name} (well-formedness {withWf}): {got}"; ok := false
      | .error m => IO.println s!"smt-check: {name}: {m}"; ok := false
  return ok

/-! The canonical order as terms, for `ordT_rel`: for pairs of values of each key type with an order term, the solver's
values of the terms are the order `Ty.cmp` computes. A comparison with its operands swapped must disagree on some
pair, so the check would see a broken encoding. -/

/-- A program's types with an enumeration `Color` (Red, Green, Blue: atoms red, green, blue) and a record `Key`. -/
def orderTypes : List TypeDecl := prelude ++
  [{ name := "m.Color", params := [], variants := [⟨"Red", []⟩, ⟨"Green", []⟩, ⟨"Blue", []⟩] },
   { name := "m.Key", params := [], variants := [⟨"Key", [⟨some "n", .int⟩, ⟨some "s", .str⟩]⟩] }]

def colorT : Ty := .adt prelude.length [] [[], [], []]
def keyT : Ty := .adt (prelude.length + 1) [] [[.int, .str]]

/-- Whether the solver's values of the order terms agree with `Ty.cmp` on each pair; with `swap` the terms compare the
second value with the first. -/
def ordAgree (solver : Solver) (t : Ty) (ht : t.isData = true) (pairs : List (t.den0 × t.den0)) (swap : Bool) :
    IO (Except String Bool) := do
  let L := Layout.addTys (fun _ => 3) {} [t]
  let some srt := L.srt? t | return .error "no sort"
  let some dts := L.datatypes? | return .error "no datatypes"
  let some (lt, le) := if swap then ordT L orderTypes t (.var 1) (.var 0) else ordT L orderTypes t (.var 0) (.var 1)
    | return .error "no order term"
  let mut all := true
  for (a, b) in pairs do
    let some va := embedV L t (Ty.up t ht a) | return .error "no value"
    let some vb := embedV L t (Ty.up t ht b) | return .error "no value"
    let script : Script :=
      { datatypes := dts
        vars := [srt, srt, Srt.bool, Srt.bool]
        asserts := [.eq (.var 0) va.term, .eq (.var 1) vb.term, .eq (.var 2) lt, .eq (.var 3) le]
        shows := [2, 3] }
    match ← solver.run script with
    | .sat vs =>
      let o := Ty.cmp orderTypes t a b
      unless (vs.lookup 2).map (·.print) == some (Val.bool (o == .lt)).print &&
          (vs.lookup 3).map (·.print) == some (Val.bool o.isLE).print do all := false
    | a => return .error s!"{repr a}"
  return .ok all

structure OrdCase where
  name : String
  t : Ty
  ht : t.isData = true
  pairs : List (t.den0 × t.den0)

def ordCases : List OrdCase :=
  [⟨"Int", .int, rfl, [((1 : Int), (2 : Int)), ((2 : Int), (1 : Int)), ((-3 : Int), (-3 : Int))]⟩,
   ⟨"String", .str, rfl, [("a", "b"), ("b", "a"), ("ab", "a"), ("z", "\u00e9"), ("x", "x")]⟩,
   ⟨"Id", .id, rfl, [(IdV.fresh 3 0, IdV.fresh 4 0), (IdV.fresh 2 5, IdV.fresh 3 0), (IdV.fresh 3 1, IdV.fresh 3 (-1)),
     (IdV.fresh 9 2, IdV.named "a"), (IdV.named "a", IdV.fresh 1 0), (IdV.named "b", IdV.named "a")]⟩,
   ⟨"#(Int, String)", .tuple [.int, .str], rfl, [(((1 : Int), "b", ()), ((1 : Int), "a", ())),
     (((0 : Int), "z", ()), ((1 : Int), "a", ())), (((2 : Int), "a", ()), ((2 : Int), "a", ()))]⟩,
   ⟨"Bool", Ty.bool, rfl, [(.inl (), .inr (.inl ())), (.inr (.inl ()), .inl ()), (.inl (), .inl ())]⟩,
   ⟨"Color", colorT, rfl, [(.inl (), .inr (.inl ())), (.inr (.inr (.inl ())), .inl ()),
     (.inr (.inl ()), .inr (.inl ()))]⟩,
   ⟨"Key", keyT, rfl, [(.inl ((1 : Int), "b", ()), .inl ((1 : Int), "a", ())),
     (.inl ((0 : Int), "z", ()), .inl ((1 : Int), "a", ()))]⟩]

def orderCheck (solver : Solver) : IO Bool := do
  let mut ok := true
  for c in ordCases do
    match ← ordAgree solver c.t c.ht c.pairs false, ← ordAgree solver c.t c.ht c.pairs true with
    | .ok true, .ok false => pure ()
    | .ok a, .ok b => IO.println s!"smt-check: order {c.name}: agrees {a}, swapped agrees {b}"; ok := false
    | .error m, _ | _, .error m => IO.println s!"smt-check: order {c.name}: {m}"; ok := false
  return ok

/-! An answer step on the pending service, for `step_encode`: the answer to the `rate` request
(shape 1) in slot 0. `rate` ensures a positive answer, its `on_answer` yields the answer plus the captured value, the
records insert that event, and the invariant `small` holds below three keys. -/

/-- v0..v4 the state, v5 the wire id, v6 the answer, then the outcome terms: v7 the slot holds the request, v8 and v9
the `ensures` rule, v10 the events, v11 the records after, v12 and v13 the invariant, v14 the pending table after.
`shift` adds to the answer the terms read, which breaks the encoding on purpose. -/
def answerScript (shift : Int) (goal : List Term) : Except String Script := do
  let L := pendingLayout
  let S := SymState.vars 0
  let t ← stepOf L pendingSites pendingSvc S (answerAt 1 0 (.var 5) (.add (.var 6) (.int shift)))
  let .answer o := t.out | throw "not an answer's terms"
  let some wf := S.wf L (v := pendingSvc) pendingShapes | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable pendingShapes) | throw "no pending sort"
  let some lsrt := L.srt? (.list .int) | throw "no events sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(rn, rh)] := o.rules | throw "not one rule"
  let [(iname, ih)] := o.finish.invariants | throw "not one invariant"
  pure { datatypes := dts,
         vars := [rsrt, .int, .int, .int, psrt, .int, .int, .bool, .bool, .str, lsrt, rsrt, .bool, .str, psrt],
         asserts := [t.codes, t.sites, t.cond, wf, .le (.int 0) (.var 5), .eq (.var 7) o.hit, .eq (.var 8) rh, .eq (.var 9) rn,
           .eq (.var 10) o.events, .eq (.var 11) o.finish.settle.terms.done.records, .eq (.var 12) ih,
           .eq (.var 13) iname, .eq (.var 14) o.finish.pending] ++ goal,
         shows := List.range 15 }

/-- The script whose goal is that no slot holds a request of the answer's type that the wire id names. -/
def unmatchedScript : Except String Script := do
  let L := pendingLayout
  let t ← stepOf L pendingSites pendingSvc (SymState.vars 0) (fun _ => pure (.unmatched .int (.var 5) (.var 6)))
  let .unmatched u := t.out | throw "not an unmatched answer's terms"
  let some wf := (SymState.vars 0).wf L (v := pendingSvc) pendingShapes | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable pendingShapes) | throw "no pending sort"
  let some dts := L.datatypes? | throw "no datatypes"
  -- Slot 0 holds a request with the wire id, so the answer names a request of another type.
  let some (S, _) := pendingSlots | throw "no layout"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, .int, .int],
         asserts := [wf, u, .le (.int 0) (.var 5), S[0]!.1, .eq (S[0]!.2[0]) (.var 5)], shows := List.range 7 }

/-- Runs the step from the decoded state and input and compares it with what the terms say; true when they agree. -/
def answerAgrees (vs : List (Nat × Val)) (unmatched : Bool) : Bool :=
  let M := modelOf vs
  let L := pendingLayout
  match (SymState.vars 0).decode M L (v := pendingSvc) prelude pendingShapes, natOf (M.vars 5), intOf (M.vars 6) with
  | some s, some to, some value =>
    let r := step prelude pendingSvc s (.answer to ⟨.int, value⟩)
    if unmatched then r.outcome.summary == "fault answerUnmatched" && r.state.pending.length == s.pending.length
    else
      let one (n h : Nat) := brokenIn M [(.var n, .var h)]
      match one 9 8, one 13 12, r.outcome with
      | n :: _, _, .invalid [n'] => n == n' && r.state.pending.length == s.pending.length
      | [], n :: _, .fault (.invariant n') => n == n'
      | [], [], .accepted =>
        let pendingAfter := decodePending L pendingShapes (M.vars 14)
        sameAs L recordsT rfl r.state.records (vs.lookup 11) && sameAs L (.list .int) rfl r.events (vs.lookup 10) &&
          pendingAfter.map (·.map (·.id)) == some (r.state.pending.map (·.id)) &&
          r.state.pending.length + 1 == s.pending.length
      | _, _, _ => false
  | _, _, _ => false

def answerCases : List (String × List Term) :=
  [ ("answer is accepted", [.var 7, .var 8, .var 12]),
    ("answer breaks the query's ensures", [.var 7, .not (.var 8)]),
    ("answer breaks the invariant", [.var 7, .var 8, .not (.var 12)]) ]

def answerCheck (solver : Solver) : IO Bool := do
  let mut ok := true
  for (name, goal) in answerCases do
    match answerScript 0 goal with
    | .error m => IO.println s!"smt-check: {name}: {m}"; ok := false
    | .ok script =>
      match ← solver.run script with
      | .sat vs => unless answerAgrees vs false do IO.println s!"smt-check: {name}: the step and the terms differ"; ok := false
      | a => IO.println s!"smt-check: {name}: {repr a}"; ok := false
  -- An encoding that reads the answer plus one must disagree with the step.
  match answerScript 1 (answerCases[0]!.2) with
  | .error m => IO.println s!"smt-check: broken answer encoding: {m}"; ok := false
  | .ok script =>
    match ← solver.run script with
    | .sat vs => if answerAgrees vs false then IO.println "smt-check: a broken answer encoding agreed with the step"; ok := false
    | a => IO.println s!"smt-check: broken answer encoding: {repr a}"; ok := false
  match unmatchedScript with
  | .error m => IO.println s!"smt-check: answer unmatched: {m}"; ok := false
  | .ok script =>
    match ← solver.run script with
    | .sat vs => unless answerAgrees vs true do IO.println "smt-check: answer unmatched: the step and the term differ"; ok := false
    | a => IO.println s!"smt-check: answer unmatched: {repr a}"; ok := false
  return ok

/-! Bounds, for `createsT_encode` and `boundReached_iff`: records of two tables of Int to Int, `a` created at most 3
times and `b` at most 2, so the table type has 3 slots and `b`'s limit is a term. The event inserts its key and value
into both. -/

def recordsB : Ty := .tuple [recordsT, recordsT]

def applyB : E (.fn [recordsB, evT] recordsB) :=
  let key : Expr [] [recordsB, evT] .int := .index (ts := [.int, .int]) (.var (.there .here)) ⟨0, by decide⟩
  let val : Expr [] [recordsB, evT] .int := .index (ts := [.int, .int]) (.var (.there .here)) ⟨1, by decide⟩
  let ins (t : Expr [] [recordsB, evT] recordsT) : Expr [] [recordsB, evT] recordsT :=
    .call (.prim .tableInsert [.int, .int] rfl) (.cons t (.cons key (.cons val .nil)))
  .lam (.tuple (.cons (ins (.index (ts := [recordsT, recordsT]) (.var .here) ⟨0, by decide⟩))
    (.cons (ins (.index (ts := [recordsT, recordsT]) (.var .here) ⟨1, by decide⟩)) .nil)))

def tableA : E (.fn [recordsB] recordsT) := .lam (.index (ts := [recordsT, recordsT]) (.var .here) ⟨0, by decide⟩)
def tableB : E (.fn [recordsB] recordsT) := .lam (.index (ts := [recordsT, recordsT]) (.var .here) ⟨1, by decide⟩)

def createsB (atMostB : Int) : List (CreateV recordsB) :=
  [⟨.int, .int, .closed tableA, 3⟩, ⟨.int, .int, .closed tableB, atMostB⟩]

def boundSvc : ServiceV :=
  { name := "b", records := recordsB, event := evT, caller := .str,
    init := ((Builtin.tableEmpty, Builtin.tableEmpty, ()) : recordsB.den0), apply := .closed applyB,
    subscribes := [⟨"x", "set", evT, .closed wrapE⟩], declares := [], commands := [], queries := [], sources := [],
    machines := [], reactions := [], invariants := .closed (.lam (.list .nil)), responses := [],
    bounds := ⟨createsB 2, 0, 0, 0⟩, scenarios := [], declared := [] }

def boundLayout : Layout :=
  let lits := Tazuna.Smt.Expr.lits applyB
  Layout.addTys (listSlots (boundSlots boundSvc.bounds) lits) {} (recordsB :: evT :: Tazuna.Smt.Expr.tys applyB ++
    Tazuna.Smt.Expr.tys tableA ++ [Ty.rules, noPending boundSvc, Ty.option (.dsl .effect [evT])])

def boundI : Fin boundSvc.subscribes.length := ⟨0, by decide⟩

/-- v0..v3 the state, v4 the value, v5 the records after, v6 the bound-reached condition, v7 the pending table. `atMostB` is the `at_most`
the script encodes for `b`, and `withLimits` whether it asserts the limits of the state before. -/
def boundScript (atMostB : Int) (withLimits : Bool) (goal : List Term) : Except String Script := do
  let L := boundLayout
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := stateAt 7
  let (o, t) ← eventTerms L [] boundSvc boundI S (.var 4)
  let (pre, cpre) ← enc (createsT L S.records (createsB atMostB))
  let (reached, creached) ← enc (boundReachedT L (createsB atMostB) t.cond o.finish.settle.terms.done.records)
  let some wf := S.wf L (v := boundSvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsB | throw "no records sort"
  let some esrt := L.srt? evT | throw "no event sort"
  let some psrt := L.srt? (noPending boundSvc) | throw "no pending sort"
  let some dts := L.datatypes? | throw "no datatypes"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, esrt, rsrt, .bool, psrt],
         asserts := [t.codes, t.sites, cpre, creached, wf] ++ (if withLimits then [pre] else []) ++
           [.eq (.var 5) o.finish.settle.terms.done.records, .eq (.var 6) reached] ++ goal,
         shows := List.range 8 }

/-- Whether the step from the decoded state and value leaves the bounds as the terms say it does. -/
def boundAgrees (vs : List (Nat × Val)) (reached : Bool) : Bool :=
  let M := modelOf vs
  let L := boundLayout
  match (stateAt 7).decode M L (v := boundSvc) prelude [],
      (SymInput.event (shs := []) (slots := 0) boundI (.var 4)).decode M L (v := boundSvc) rfl with
  | some s, some x =>
    let r := step prelude boundSvc s x
    within boundSvc.bounds.creates s.records && r.outcome.summary == "accepted" &&
      within boundSvc.bounds.creates r.state.records == !reached &&
      (reached || sameAs L recordsB rfl r.state.records (vs.lookup 5))
  | _, _ => false

def boundCheck (solver : Solver) : IO Bool := do
  let mut ok := true
  if (boundLayout.find? recordsT).map (·.2) != some 3 then IO.println "smt-check: bounds: not 3 slots"; ok := false
  for (name, reached) in [("a step leaves a create's bound", true), ("a step stays within the bounds", false)] do
    -- The step's own condition holds, so only the limit can make the bound reached.
    let goal := if reached then [.var 6] else [.not (.var 6)]
    match boundScript 2 true goal with
    | .error m => IO.println s!"smt-check: {name}: {m}"; ok := false
    | .ok script =>
      match ← solver.run script with
      | .sat vs => unless boundAgrees vs reached do IO.println s!"smt-check: {name}: the step and the terms differ"; ok := false
      | a => IO.println s!"smt-check: {name}: {repr a}"; ok := false
  -- Three keys in `b` break its limit: unsat with the limits, sat without them.
  let some (d, n) := boundLayout.find? recordsT | IO.println "smt-check: bounds: no table"; return false
  let some (dt, _) := boundLayout.find? (.tuple [Ty.bool, .int, .int]) | IO.println "smt-check: bounds: no slot"; return false
  let some (dr, _) := boundLayout.find? recordsB | IO.println "smt-check: bounds: no records"; return false
  let full := allT ((slotsOf d dt n 2 (.sel dr 0 1 (.var 0))).map (·.1))
  for (withLimits, want) in [(true, "unsat"), (false, "sat")] do
    match boundScript 2 withLimits [full] with
    | .ok script =>
      let got := match ← solver.run script with
        | .unsat => "unsat"
        | .sat _ => "sat"
        | _ => "unknown"
      if got != want then IO.println s!"smt-check: limits exclude a full b (limits {withLimits}): {got}"; ok := false
    | .error m => IO.println s!"smt-check: bounds: {m}"; ok := false
  -- A limit encoded with the wrong `at_most` must disagree with the step.
  match boundScript 1 false [.var 6, .not (.lt (.int 1) (sizeT (slotsOf d dt n 2 (.sel dr 0 1 (.var 0)))))] with
  | .error m => IO.println s!"smt-check: broken limit: {m}"; ok := false
  | .ok script =>
    match ← solver.run script with
    | .sat vs => if boundAgrees vs true then IO.println "smt-check: a broken limit agreed with the step"; ok := false
    | a => IO.println s!"smt-check: broken limit: {repr a}"; ok := false
  return ok

/-! An effect value as its kind's variant: `request_command(external_command("send"), x + k, fn(_) { [x] })` with
`x` free, the `on_answer` site m:3:7 capturing `x`. The layout lists a second kind first, at another site, so the
variant index is not 0 by accident. The solver's value of the effect must be the variant of the effect `eval` builds
at the solver's `x`: the same kind (name and site), the input, and the captured value. -/

def effArgs : List Ty := [.int, .int, Ty.nil, Ty.nil]
def answerTyE : Ty := .fn [Ty.result Ty.nil Ty.nil] (.list .int)

def sendE (k : Int) : Expr [] [.int] (.dsl .effect [.int]) :=
  let handle : Expr [] [.int] (.dsl .externalCommand [.int, Ty.nil, Ty.nil]) :=
    .call (.prim .externalCommand [.int, Ty.nil, Ty.nil] rfl) (.cons (.str "send") .nil)
  let body : Expr [] [.int] answerTyE := .lam (.list (.cons (.var (.there .here)) .nil))
  let clo : Expr [] [.int] (.dsl .closure [answerTyE]) := .close ⟨"m", 3, 7, 0⟩ (.cons (.var .here) .nil) rfl rfl body
  .call (.prim .requestCommand effArgs rfl) (.cons handle (.cons (.bin .add (.var .here) (.int k)) (.cons clo .nil)))

def sendKey (site : SiteId) : EffectKey :=
  ⟨.int, "send", .int, Ty.nil, some Ty.nil, none, ⟨site, [.int]⟩⟩

def effLayout : Layout :=
  Layout.addEffects (fun _ => 2) (Layout.addTys (fun _ => 2) { effects := [sendKey ⟨"m", 9, 9, 0⟩, sendKey ⟨"m", 3, 7, 0⟩] }
    [.dsl .effect [.int], .int])

/-- Whether the solver's value `v` is the variant of the effect `eff` holds: its kind's name and site, its input and
the value its `on_answer` captured, all Ints here. -/
def effMatches (L : Layout) (eff : EffectV .int) (v : Val) : Bool :=
  match eff, v with
  | .request r, .ctor _ k [vi, _, .ctor _ 0 va] =>
    match (L.effectsOf .int)[k]?, Ty.same r.input .int, Ty.sames r.onAnswer.Γ [.int] with
    | some key, some ⟨hi⟩, some ⟨hg⟩ =>
      let x : Int := cast (congrArg Ty.den0 hi) r.value
      let env : Int := (cast (congrArg (fun Γ => (Ty.tuple Γ).den0) hg) r.onAnswer.env).1
      key.name == r.name && key.answer.site == r.onAnswer.site && vi.print == (Val.int x).print &&
        (va.map (·.print)) == [(Val.int env).print]
    | _, _, _ => false
  | _, _ => false

def effectCheck (solver : Solver) : IO Bool := do
  let L := effLayout
  let some srt := L.srt? (.dsl .effect [.int]) | IO.println "smt-check: effect: no sort"; return false
  let some dts := L.datatypes? | IO.println "smt-check: effect: no datatypes"; return false
  match encode L (G := []) () (sendE 1) (Term.var 1, ()) with
  | .error r => IO.println s!"smt-check: effect: no encoding: {repr r}"; return false
  | .ok (code, cond) =>
    let script : Script :=
      { datatypes := dts, vars := [srt, .int], asserts := [.eq (.var 0) code, .lt (.int 40) (.var 1), cond],
        shows := [0, 1] }
    match ← solver.run script with
    | .sat vs =>
      match vs.lookup 0, vs.lookup 1 with
      | some v, some (.int x) =>
        let eval (k : Int) : EffectV .int := (sendE k).eval (G := []) .nil () (x, ())
        -- The comparison must tell effects apart: the effect of `x + 2` is not the solver's.
        if !effMatches L (eval 1) v then
          IO.println s!"smt-check: effect: the solver's {v.print} is not eval's effect at x = {x}"; return false
        if effMatches L (eval 2) v then
          IO.println "smt-check: effect: the comparison accepts another input"; return false
        return true
      | _, _ => IO.println "smt-check: effect: no values"; return false
    | a => IO.println s!"smt-check: effect: {repr a}"; return false

/-! An own effect as its kind's variant: `send_command(put, "alice", x + k, fn(_) { [#(x, x)] })` with `put` the
command above and `x` free, the `on_answer` site m:4:2 capturing `x`. The layout lists a request kind of the same
event type and another own kind first, so the variant index is past both by construction, not by accident. The
solver's value must be the variant of the effect `eval` builds at the solver's `x`: the command's name and the site,
the caller, the input and the captured value. -/

def putHandleT : Ty := .dsl .command [recordsT, evT, .str, .int, .str]
def putAnswerT : Ty := .fn [Ty.result Ty.nil .str] (.list evT)

def sendPutE (k : Int) : Expr [] [putHandleT, .int] (.dsl .effect [evT]) :=
  let x : Expr [] [putHandleT, .int] .int := .var (.there .here)
  let body : Expr [] [.int] putAnswerT :=
    .lam (.list (.cons (.tuple (.cons (.var (.there .here)) (.cons (.var (.there .here)) .nil))) .nil))
  let clo : Expr [] [putHandleT, .int] (.dsl .closure [putAnswerT]) := .close ⟨"m", 4, 2, 0⟩ (.cons x .nil) rfl rfl body
  .call (.prim .sendCommand [recordsT, evT, .str, .int, .str] rfl)
    (.cons (.var .here) (.cons (.str "alice") (.cons (.bin .add x (.int k)) (.cons clo .nil))))

def ownLayout : Layout :=
  Layout.addEffects (fun _ => 2) (Layout.addTys (fun _ => 2)
    { effects := [⟨evT, "send", .int, Ty.nil, some Ty.nil, none, ⟨⟨"m", 9, 9, 0⟩, [.int]⟩⟩],
      owns := [.command evT "put" .str .int .str ⟨⟨"m", 8, 8, 0⟩, [.int]⟩,
        .command evT "put" .str .int .str ⟨⟨"m", 4, 2, 0⟩, [.int]⟩] }
    [.dsl .effect [evT], .int, evT, .tuple [.int]])

/-- Whether the solver's value `v` is the variant of the own effect `eff`: its kind's name and site after the request
kinds, its caller, its input and the value its `on_answer` captured. -/
def ownMatches (L : Layout) (eff : EffectV evT) (v : Val) : Bool :=
  match eff, v with
  | .command name c i _ caller value onAnswer, .ctor _ idx [vc, vi, .ctor _ 0 va] =>
    match (L.ownsOf evT)[idx - (L.effectsOf evT).length]?, Ty.same c .str, Ty.same i .int,
        Ty.sames onAnswer.Γ [.int] with
    | some (.command _ kn _ _ _ ka), some ⟨hc⟩, some ⟨hi⟩, some ⟨hg⟩ =>
      let cl : String := cast (congrArg Ty.den0 hc) caller
      let x : Int := cast (congrArg Ty.den0 hi) value
      let env : Int := (cast (congrArg (fun Γ => (Ty.tuple Γ).den0) hg) onAnswer.env).1
      idx ≥ (L.effectsOf evT).length && kn == name && ka.site == onAnswer.site && vc.print == (Val.str cl).print &&
        vi.print == (Val.int x).print && (va.map (·.print)) == [(Val.int env).print]
    | _, _, _, _ => false
  | _, _ => false

def ownEffectCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: own effect: {m}"; return false
  let L := ownLayout
  let some srt := L.srt? (.dsl .effect [evT]) | fail "no sort"
  let some dts := L.datatypes? | fail "no datatypes"
  match encode L (G := []) () (sendPutE 1) (putC.name, Term.var 1, ()) with
  | .error r => fail s!"no encoding: {repr r}"
  | .ok (code, cond) =>
    let script : Script :=
      { datatypes := dts, vars := [srt, .int], asserts := [.eq (.var 0) code, .lt (.int 40) (.var 1), cond],
        shows := [0, 1] }
    match ← solver.run script with
    | .sat vs =>
      match vs.lookup 0, vs.lookup 1 with
      | some v, some (.int x) =>
        let eval (k : Int) : EffectV evT := (sendPutE k).eval (G := []) .nil () (⟨putC, rfl, rfl⟩, x, ())
        if !ownMatches L (eval 1) v then return ← fail s!"the solver's {v.print} is not eval's effect at x = {x}"
        if ownMatches L (eval 2) v then return ← fail "the comparison accepts another input"
        return true
      | _, _ => fail "no values"
    | a => fail s!"{repr a}"

/-! A list of effects, as a reaction returns one: `[request_command(send, x + 1, fn(_) { [x] })]` in two slots. The
free slot holds some value of the effect datatype, which no value reads; the occupied one must be eval's effect. -/

def sendsE (k : Int) : Expr [] [.int] (.list (.dsl .effect [.int])) := .list (.cons (sendE k) .nil)

def effListLayout : Layout :=
  Layout.addEffects (fun _ => 2) (Layout.addTys (fun _ => 2) { effects := [sendKey ⟨"m", 9, 9, 0⟩, sendKey ⟨"m", 3, 7, 0⟩] }
    [.list (.dsl .effect [.int]), .int])

/-- The items of a list's occupied slots. -/
def occupied : Val → List Val
  | .ctor _ 0 slots => slots.filterMap fun | .ctor _ 0 [.bool true, x] => some x | _ => none
  | _ => []

def effectListCheck (solver : Solver) : IO Bool := do
  let L := effListLayout
  let some srt := L.srt? (.list (.dsl .effect [.int])) | IO.println "smt-check: effect list: no sort"; return false
  let some dts := L.datatypes? | IO.println "smt-check: effect list: no datatypes"; return false
  match encode L (G := []) () (sendsE 1) (Term.var 1, ()) with
  | .error r => IO.println s!"smt-check: effect list: no encoding: {repr r}"; return false
  | .ok (code, cond) =>
    let script : Script :=
      { datatypes := dts, vars := [srt, .int], asserts := [.eq (.var 0) code, .lt (.int 40) (.var 1), cond],
        shows := [0, 1] }
    match ← solver.run script with
    | .sat vs =>
      match vs.lookup 0, vs.lookup 1 with
      | some v, some (.int x) =>
        let eval (k : Int) : List (EffectV .int) := (sendsE k).eval (G := []) .nil () (x, ())
        let agrees (k : Int) : Bool := match eval k, occupied v with
          | [eff], [w] => effMatches L eff w
          | _, _ => false
        if !agrees 1 then
          IO.println s!"smt-check: effect list: the solver's {v.print} is not eval's list at x = {x}"; return false
        if agrees 2 then
          IO.println "smt-check: effect list: the comparison accepts another input"; return false
        return true
      | _, _ => IO.println "smt-check: effect list: no values"; return false
    | a => IO.println s!"smt-check: effect list: {repr a}"; return false

/-! A machine's `effect` from its kept source: `fn(ctx) { case ctx.state == 5 { True ->
Some(request_command(send, ctx.key + 1, fn(_) { [ctx.key] }))  False -> None } }`, its `on_answer` at m:3:7 capturing
the key. Applied to the code of a context with a free key and state, the solver's value must be what the machine
starts on entering that state (`MachineV.effectAt`), once with the state 5 and once without. -/

def mctxT : Ty := Ty.machineCtx .int .int .int

def machineEffectE : Expr [] [] (.fn [mctxT] (Ty.option (.dsl .effect [.int]))) :=
  let ctx : Expr [] [mctxT] mctxT := .var .here
  let key : Expr [] [mctxT] .int := .field (ft := .int) "key" 0 (by simp) ctx
  let st : Expr [] [mctxT] .int := .field (ft := .int) "state" 1 (by simp) ctx
  let handle : Expr [] [mctxT] (.dsl .externalCommand [.int, Ty.nil, Ty.nil]) :=
    .call (.prim .externalCommand [.int, Ty.nil, Ty.nil] rfl) (.cons (.str "send") .nil)
  let body : Expr [] [.int] answerTyE := .lam (.list (.cons (.var (.there .here)) .nil))
  let clo : Expr [] [mctxT] (.dsl .closure [answerTyE]) := .close ⟨"m", 3, 7, 0⟩ (.cons key .nil) rfl rfl body
  let req : Expr [] [mctxT] (.dsl .effect [.int]) :=
    .call (.prim .requestCommand effArgs rfl) (.cons handle (.cons (.bin .add key (.int 1)) (.cons clo .nil)))
  .lam (.case (.bin (.eq rfl) st (.int 5))
    (.cons (.ctor (vs := [[], []]) ⟨0, by decide⟩ .nil) (.ctor (vs := [[Ty.dsl .effect [.int]], []]) ⟨0, by decide⟩ (.cons req .nil))
      (.cons (.ctor (vs := [[], []]) ⟨1, by decide⟩ .nil) (.ctor (vs := [[Ty.dsl .effect [.int]], []]) ⟨1, by decide⟩ .nil) .nil))
    ⟨4, rfl⟩)

def effectM : MachineV .int .int :=
  { name := "m", key := .int, state := .int, instances := .closed (.lam (.call (.prim .bagFromList [.int] rfl)
      (.cons (.list .nil) .nil))), initial := (0 : Int), on := .closed (.lam (.ctor (vs := [[], [.int]]) ⟨0, by decide⟩ .nil)),
    after := .closed (.lam (.ctor (vs := [[Ty.timer .int], []]) ⟨1, by decide⟩ .nil)), effect := .closed machineEffectE,
    invariants := .closed (.lam (.list .nil)) }

def machineEffectLayout : Layout :=
  Layout.addTys (fun _ => 2) { effects := [sendKey ⟨"m", 9, 9, 0⟩, sendKey ⟨"m", 3, 7, 0⟩] }
    [mctxT, Ty.option (.dsl .effect [.int]), .tuple [.int]]

def machineEffectCheck (solver : Solver) : IO Bool := do
  let L := machineEffectLayout
  let some srt := L.srt? (Ty.option (.dsl .effect [.int])) | IO.println "smt-check: machine effect: no sort"; return false
  let some dts := L.datatypes? | IO.println "smt-check: machine effect: no datatypes"; return false
  let some (dctx, _) := L.find? mctxT | IO.println "smt-check: machine effect: no context"; return false
  let ctxT : Term := .ctor dctx 0 [.var 1, .var 2, .int 0, .int 0]
  let mut ok := true
  for five in [true, false] do
    match effectM.effect.code L >>= fun (f, c) => (f (ctxT, ())).map fun (o, c') => (o, andT c c') with
    | .error r => IO.println s!"smt-check: machine effect: no encoding: {repr r}"; return false
    | .ok (o, cond) =>
      let stAssert : Term := if five then .eq (.var 2) (.int 5) else .not (.eq (.var 2) (.int 5))
      let script : Script :=
        { datatypes := dts, vars := [srt, .int, .int], asserts := [.eq (.var 0) o, stAssert, cond], shows := [0, 1, 2] }
      match ← solver.run script with
      | .sat vs =>
        match vs.lookup 0, vs.lookup 1, vs.lookup 2 with
        | some v, some (.int key), some (.int st) =>
          let agrees (k : Int) : Bool := match effectM.effectAt k st (0 : Int) 0, v with
            | some eff, .ctor _ 0 [w] => effMatches L eff w
            | none, .ctor _ 1 [] => true
            | _, _ => false
          if !agrees key then
            IO.println s!"smt-check: machine effect: the solver's {v.print} is not the effect at key {key}, state {st}"
            ok := false
          -- The comparison must tell effects apart: another key's effect is not the solver's.
          if five && agrees (key + 1) then
            IO.println "smt-check: machine effect: the comparison accepts another key"; ok := false
        | _, _, _ => IO.println "smt-check: machine effect: no values"; ok := false
      | a => IO.println s!"smt-check: machine effect: {repr a}"; ok := false
  return ok

/-! T5's timer question for one machine (`backQuestions`), with `after` from its kept source over Int keys, states and
records. `forwardE` sets `Timer(ctx.state, ctx.state)` where the state is not negative and no timer otherwise, so its
target question is unsat; `backE` sets `Timer(ctx.key, ctx.state)`, so a negative key sets a timer before the time and
the target question is sat, and the model's context must be one where Lean's `after` sets such a timer. Nothing has
slots here, so both bound questions are unsat. -/

def timerAfterE (delay : Expr [] [mctxT] .int) (guard : Bool) : Expr [] [] (.fn [mctxT] (Ty.option (Ty.timer .int))) :=
  let ctx : Expr [] [mctxT] mctxT := .var .here
  let st : Expr [] [mctxT] .int := .field (ft := .int) "state" 1 (by simp) ctx
  let some' : Expr [] [mctxT] (Ty.option (Ty.timer .int)) := .ctor (vs := [[Ty.timer .int], []]) ⟨0, by decide⟩
    (.cons (.ctor (vs := [[.int, .int]]) ⟨0, by decide⟩ (.cons delay (.cons st .nil))) .nil)
  let none' : Expr [] [mctxT] (Ty.option (Ty.timer .int)) := .ctor (vs := [[Ty.timer .int], []]) ⟨1, by decide⟩ .nil
  if guard then
    .lam (.case (.bin .lt st (.int 0))
      (.cons (.ctor (vs := [[], []]) ⟨0, by decide⟩ .nil) none' (.cons (.ctor (vs := [[], []]) ⟨1, by decide⟩ .nil) some' .nil))
      ⟨4, rfl⟩)
  else .lam some'

def timerM (af : Expr [] [] (.fn [mctxT] (Ty.option (Ty.timer .int)))) : MachineV .int .int :=
  { name := "t", key := .int, state := .int, instances := effectM.instances, initial := (0 : Int), on := effectM.on,
    after := .closed af, effect := .closed (.lam (.ctor (vs := [[Ty.dsl .effect [.int]], []]) ⟨1, by decide⟩ .nil)),
    invariants := effectM.invariants }

def forwardE : Expr [] [] (.fn [mctxT] (Ty.option (Ty.timer .int))) :=
  timerAfterE (.field (ft := .int) "state" 1 (by simp) (.var .here)) true
def backE : Expr [] [] (.fn [mctxT] (Ty.option (Ty.timer .int))) :=
  timerAfterE (.field (ft := .int) "key" 0 (by simp) (.var .here)) false

def timerLayout : Layout :=
  Layout.addTys (fun _ => 2) {} [mctxT, Ty.option (Ty.timer .int), Ty.timer .int, Ty.option (.tuple [.int, .int]),
    .tuple [.int, .int], Ty.bool]

def timerCheck (solver : Solver) : IO Bool := do
  let mut ok := true
  for (name, af, back) in [("forward", forwardE, false), ("back", backE, true)] do
    match backQuestions timerLayout (timerM af) with
    | .error r => IO.println s!"smt-check: timer {name}: no questions: {repr r}"; ok := false
    | .ok (bq, tq) =>
      match ← solver.run bq with
      | .unsat => pure ()
      | a => IO.println s!"smt-check: timer {name}: bound question not unsat: {repr a}"; ok := false
      match ← solver.run tq, back with
      | .unsat, false => pure ()
      | .sat vs, true =>
        match vs.lookup 0, vs.lookup 1, vs.lookup 2, vs.lookup 3 with
        | some (.int key), some (.int st), some (.int recs), some (.int now) =>
          match Step.timerAt now ((timerM af).after.fn (.inl (key, st, recs, now, ()), ())) with
          | some (d, _) => unless d < now do
              IO.println s!"smt-check: timer back: Lean's timer at {d} is not before {now}"; ok := false
          | none => IO.println "smt-check: timer back: Lean's after sets no timer"; ok := false
        | _, _, _, _ => IO.println "smt-check: timer back: no values"; ok := false
      | a, _ => IO.println s!"smt-check: timer {name}: target question: {repr a}"; ok := false
  return ok

/-! Machine invariants over the instance table: `fn(ctx) { [#(case ctx.key == 1 { True -> "one" False -> "other" },
ctx.state < 5)] }`. Slot 0 holds key 3 and slot 1 key 1, both in a state that breaks the rule, so the step reports
"one" before "other" (key order), while slot order gives the reverse. The names read from the model must be the
broken invariants of the decoded instances, in their order; slot order must not pass the comparison. -/

def invCtxT : Ty := Ty.machineCtx .int .int recordsT

def invM : MachineV recordsT .int :=
  let ctx : Expr [] [invCtxT] invCtxT := .var .here
  let key : Expr [] [invCtxT] .int := .field (ft := .int) "key" 0 (by simp) ctx
  let st : Expr [] [invCtxT] .int := .field (ft := .int) "state" 1 (by simp) ctx
  let name : Expr [] [invCtxT] .str := .case (.bin (.eq rfl) key (.int 1))
    (.cons (.ctor (vs := [[], []]) ⟨0, by decide⟩ .nil) (.str "one")
      (.cons (.ctor (vs := [[], []]) ⟨1, by decide⟩ .nil) (.str "other") .nil)) ⟨4, rfl⟩
  { doorM with name := "inv", invariants := .closed (.lam (.list (.cons (.tuple (.cons name
      (.cons (.bin .lt st (.int 5)) .nil))) .nil))) }

def invSvc : ServiceV := { querySvc with name := "i", queries := [], machines := [invM] }

def invLayout : Layout :=
  Layout.addTys (fun _ => 3) {} [recordsT, invM.table, Ty.machineCtx .int .int recordsT, Ty.rules, noPending querySvc]

def invariantCheck (solver : Solver) : IO Bool := do
  let L := invLayout
  let some (d, n) := L.find? invM.table | IO.println "smt-check: machine invariants: no table"; return false
  let some (dt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | IO.println "smt-check: machine invariants: no slot"; return false
  let some (de, _) := L.find? (instEntry .int) | IO.println "smt-check: machine invariants: no entry"; return false
  let some wf := (SymState.vars 0).wf L (v := invSvc) [] | IO.println "smt-check: machine invariants: no wf"; return false
  let some rsrt := L.srt? recordsT | IO.println "smt-check: machine invariants: no records sort"; return false
  let some msrt := L.srt? invM.table | IO.println "smt-check: machine invariants: no table sort"; return false
  let some psrt := L.srt? (noPending querySvc) | IO.println "smt-check: machine invariants: no pending sort"; return false
  let some dts := L.datatypes? | IO.println "smt-check: machine invariants: no datatypes"; return false
  match invM.invariants.code L >>= fun (inv, c0) =>
      (encodeInstInvariants L prelude invM inv (.var 5) (.var 0) (.var 1)).map fun (cs, c) => (cs, andT c0 c) with
  | .error r => IO.println s!"smt-check: machine invariants: no encoding: {repr r}"; return false
  | .ok (checks, cond) =>
    let S := slotsOf d dt n 2 (.var 5)
    let key (j : Nat) := S[j]!.2[0]
    let state (j : Nat) := Term.sel de 0 0 (S[j]!.2[1])
    let goal := [S[0]!.1, S[1]!.1, .not S[2]!.1, .eq (key 0) (.int 3), .eq (state 0) (.int 7), .eq (key 1) (.int 1),
      .eq (state 1) (.int 9)]
    let script : Script :=
      { datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt], asserts := wf :: cond :: goal,
        shows := List.range 6 }
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let some s := (SymState.vars 0).decode M L (v := invSvc) prelude []
        | IO.println "smt-check: machine invariants: the model does not decode"; return false
      let step := s.machines.toSigma.flatMap fun ⟨m, insts⟩ => insts.flatMap fun i =>
        Step.broken (m.invariants.fn (.inl (i.key, i.state, s.records, s.now, ()), ()))
      let read := instBroken L prelude M invM.key checks
      let inSlots := (checks.filter fun c => (c.occupied.denote M).toBool).flatMap (brokenIn M ·.rules)
      let mut ok := true
      if read != step || step != ["one", "other"] then
        IO.println s!"smt-check: machine invariants: read {read}, the step's {step}"; ok := false
      if inSlots == step then
        IO.println "smt-check: machine invariants: slot order passes the comparison"; ok := false
      return ok
    | a => IO.println s!"smt-check: machine invariants: {repr a}"; return false

/-! A machine's reaction to an event as a new instance table: instances are the records' keys {3, 5}; the old table
holds key 3 in state 0 and key 7 in state 1. `on` enters 1 from state 0, `after` starts a timer (5 ms, to state 2) in
state 1. So key 3 enters 1 with a timer due at now + 5, key 5 starts at 0 without one, and key 7 goes. The decoded new
table's instances must be the step's (`machineStep`); the step from no instances (key 3 starting afresh) must differ. -/

def reactM : MachineV recordsT .int :=
  let st : Expr [] [invCtxT, .int] .int := .field (ft := .int) "state" 1 (by simp) (.var .here)
  let st1 : Expr [] [invCtxT] .int := .field (ft := .int) "state" 1 (by simp) (.var .here)
  { invM with
    name := "react"
    on := .closed (.lam (.case (.bin (.eq rfl) st (.int 0))
      (.cons (.ctor (vs := [[], []]) ⟨0, by decide⟩ .nil) (.ctor (vs := [[], [.int]]) ⟨1, by decide⟩ (.cons (.int 1) .nil))
        (.cons (.ctor (vs := [[], []]) ⟨1, by decide⟩ .nil) (.ctor (vs := [[], [.int]]) ⟨0, by decide⟩ .nil) .nil)) ⟨4, rfl⟩))
    after := .closed (.lam (.case (.bin (.eq rfl) st1 (.int 1))
      (.cons (.ctor (vs := [[], []]) ⟨0, by decide⟩ .nil) (.ctor (vs := [[Ty.timer .int], []]) ⟨0, by decide⟩
          (.cons (.ctor (vs := [[.int, .int]]) ⟨0, by decide⟩ (.cons (.int 5) (.cons (.int 2) .nil))) .nil))
        (.cons (.ctor (vs := [[], []]) ⟨1, by decide⟩ .nil) (.ctor (vs := [[Ty.timer .int], []]) ⟨1, by decide⟩ .nil) .nil)) ⟨4, rfl⟩)) }

def reactSvc : ServiceV := { querySvc with name := "r", queries := [], machines := [reactM] }

def reactTys : List Ty :=
  [recordsT, reactM.table, .bag .int, invCtxT, Ty.next .int, Ty.option (Ty.timer .int), Ty.timer .int,
    Ty.option (.tuple [.int, .int]), .tuple [.int, .int], instEntry .int, Ty.option (.dsl .effect [.int]),
    noPending querySvc]

def reactLayout : Layout := Layout.addTys (fun _ => 3) {} reactTys

def reactCheck (solver : Solver) : IO Bool := do
  let L := reactLayout
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: machine reaction: {m}"; return false
  let some (d, n) := L.find? reactM.table | fail "no table"
  let some (dt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no slot"
  let some (de, _) := L.find? (instEntry .int) | fail "no entry"
  let some (dopt, _) := L.find? (Ty.option (.tuple [.int, .int])) | fail "no timer option"
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some wf := (SymState.vars 0).wf L (v := reactSvc) [] | fail "no wf"
  let some rsrt := L.srt? recordsT | fail "no records sort"
  let some msrt := L.srt? reactM.table | fail "no table sort"
  let some psrt := L.srt? (noPending querySvc) | fail "no pending sort"
  let some dts := L.datatypes? | fail "no datatypes"
  match ReactCode.of L reactM >>= fun (rc, c0) =>
      (encodeReact L reactM rc (.var 5) (.var 0) (.var 1) (.var 7)).map fun (o, c) => (o.table, andT c0 c) with
  | .error r => fail s!"no encoding: {repr r}"
  | .ok (newT, cond) =>
    let So := slotsOf d dt n 2 (.var 5)
    let Sr := slotsOf dr drt nr 2 (.var 0)
    let key (j : Nat) := So[j]!.2[0]
    let state (j : Nat) := Term.sel de 0 0 (So[j]!.2[1])
    let timer (j : Nat) := Term.sel de 0 1 (So[j]!.2[1])
    let goal := [So[0]!.1, So[1]!.1, .not So[2]!.1, .eq (key 0) (.int 3), .eq (state 0) (.int 0), .is dopt 1 (timer 0),
      .eq (key 1) (.int 7), .eq (state 1) (.int 1), .is dopt 1 (timer 1), Sr[0]!.1, Sr[1]!.1, .not Sr[2]!.1,
      .eq (Sr[0]!.2[0]) (.int 5), .eq (Sr[1]!.2[0]) (.int 3), .eq (.var 1) (.int 100),
      .eq (.var 6) newT]
    let script : Script :=
      { datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt, msrt, .int], asserts := wf :: cond :: goal,
        shows := List.range 8 }
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let some s := (SymState.vars 0).decode M L (v := reactSvc) prelude [] | fail "the model does not decode"
      let some tbl := decodeV L reactM.table ((Term.var 6).denote M) | fail "the new table does not decode"
      let some (.int ev) := vs.lookup 7 | fail "no event"
      let read := instancesOf prelude reactM (Ty.down _ reactM.table_data tbl)
      let some [⟨m, insts⟩] := some s.machines.toSigma | fail "not one machine"
      let view {r e : Ty} (m : MachineV r e) (is : List (Step.Instance m)) := is.map fun i =>
        (intDen _ i.key, intDen _ i.state, i.timer.map fun (d, st) => (d, intDen _ st))
      let step (insts : List (Step.Instance m)) :=
        view m (Step.machineStep (e := reactSvc.event) prelude s.records s.now ev m insts).1
      let mut ok := true
      if view reactM read != step insts || view reactM read != [(some 3, some 1, some (105, some 2)), (some 5, some 0, none)] then
        ok ← fail s!"the new table holds {view reactM read}, the step {step insts}"
      if view reactM read == step [] then ok ← fail "the step from no instances passes the comparison"
      return ok
    | a => fail s!"{repr a}"

/-! A staying instance whose `after` would outgrow a slot: `after` builds a four-item list, one more than the three
slots of every type, so wherever it is evaluated the bound is reached. `on` always stays. With key 3 in the old table
in state 1 and in the records, the instance stays and `after` is not evaluated, so the step is within the bounds and
the script must be sat with the step's table; with key 3 missing from the old table it starts afresh, `after` is
evaluated, and the script must be unsat. -/

def stayM : MachineV recordsT .int :=
  { reactM with
    name := "stay"
    on := .closed (.lam (.ctor (vs := [[], [.int]]) ⟨0, by decide⟩ .nil))
    after := .closed (.lam (.let_ (.list (.cons (.int 1) (.cons (.int 2) (.cons (.int 3) (.cons (.int 4) .nil)))))
      (.ctor (vs := [[Ty.timer .int], []]) ⟨1, by decide⟩ .nil))) }

def staySvc : ServiceV := { querySvc with name := "s", queries := [], machines := [stayM] }

def stayLayout : Layout := Layout.addTys (fun _ => 3) {} (reactTys ++ [.list .int])

def stayCheck (solver : Solver) : IO Bool := do
  let L := stayLayout
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: staying instance: {m}"; return false
  let some (d, n) := L.find? stayM.table | fail "no table"
  let some (dt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no slot"
  let some (de, _) := L.find? (instEntry .int) | fail "no entry"
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some wf := (SymState.vars 0).wf L (v := staySvc) [] | fail "no wf"
  let some rsrt := L.srt? recordsT | fail "no records sort"
  let some msrt := L.srt? stayM.table | fail "no table sort"
  let some psrt := L.srt? (noPending querySvc) | fail "no pending sort"
  let some dts := L.datatypes? | fail "no datatypes"
  match ReactCode.of L stayM >>= fun (rc, c0) =>
      (encodeReact L stayM rc (.var 5) (.var 0) (.var 1) (.var 7)).map fun (o, c) => (o.table, andT c0 c) with
  | .error r => fail s!"no encoding: {repr r}"
  | .ok (newT, cond) =>
    let So := slotsOf d dt n 2 (.var 5)
    let Sr := slotsOf dr drt nr 2 (.var 0)
    let records := [Sr[0]!.1, .not Sr[1]!.1, .not Sr[2]!.1, .eq (Sr[0]!.2[0]) (.int 3), .eq (.var 6) newT]
    let script (old : List Term) : Script :=
      { datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt, msrt, .int],
        asserts := wf :: cond :: old ++ records, shows := List.range 8 }
    let stays := [So[0]!.1, .not So[1]!.1, .not So[2]!.1, .eq (So[0]!.2[0]) (.int 3),
      .eq (Term.sel de 0 0 (So[0]!.2[1])) (.int 1)]
    let stayed ← match ← solver.run (script stays) with
    | .sat vs => do
      let M := modelOf vs
      let some s := (SymState.vars 0).decode M L (v := staySvc) prelude [] | fail "the model does not decode"
      let some tbl := decodeV L stayM.table ((Term.var 6).denote M) | fail "the new table does not decode"
      let some (.int ev) := vs.lookup 7 | fail "no event"
      let read := instancesOf prelude stayM (Ty.down _ stayM.table_data tbl)
      let some [⟨m, insts⟩] := some s.machines.toSigma | fail "not one machine"
      let view {r e : Ty} (m : MachineV r e) (is : List (Step.Instance m)) := is.map fun i =>
        (intDen _ i.key, intDen _ i.state, i.timer.map fun (d, st) => (d, intDen _ st))
      let step (insts : List (Step.Instance m)) :=
        view m (Step.machineStep (e := staySvc.event) prelude s.records s.now ev m insts).1
      if view stayM read != step insts || (view stayM read).map (fun (k, st, _) => (k, st)) != [((some 3 : Option Int), (some 1 : Option Int))] then
        return ← fail s!"the new table holds {view stayM read}, the step {step insts}"
      if view stayM read == step [] then return ← fail "the step from no instances passes the comparison"
      return true
    | a => fail s!"the instance stays, yet the script is {repr a}"
    let mut ok := stayed
    match ← solver.run (script [.not So[0]!.1, .not So[1]!.1, .not So[2]!.1]) with
    | .unsat => pure ()
    | a => ok ← fail s!"the instance starts and after outgrows a slot, yet the script is {repr a}"
    return ok

/-! The effects a machine's instances start on an event, with their wire ids: the reaction above, whose `effect` is
`fn(ctx) { Some(request_command(send, ctx.key + 1, fn(_) { [ctx.key] })) }` on entering any state. Key 3 enters 1 and
key 5 starts, so both start an effect; the bag holds 5 in slot 0 and 3 in slot 1, and the next wire id is 40. The
effect slots read from the model must hold the step's effects with the ids `start` gives them (key 3's 40, key 5's
41), and the count term their number; ids by slot order must not pass the comparison. -/

def startEffectE : Expr [] [] (.fn [invCtxT] (Ty.option (.dsl .effect [.int]))) :=
  let ctx : Expr [] [invCtxT] invCtxT := .var .here
  let key : Expr [] [invCtxT] .int := .field (ft := .int) "key" 0 (by simp) ctx
  let handle : Expr [] [invCtxT] (.dsl .externalCommand [.int, Ty.nil, Ty.nil]) :=
    .call (.prim .externalCommand [.int, Ty.nil, Ty.nil] rfl) (.cons (.str "send") .nil)
  let body : Expr [] [.int] answerTyE := .lam (.list (.cons (.var (.there .here)) .nil))
  let clo : Expr [] [invCtxT] (.dsl .closure [answerTyE]) := .close ⟨"m", 3, 7, 0⟩ (.cons key .nil) rfl rfl body
  let req : Expr [] [invCtxT] (.dsl .effect [.int]) :=
    .call (.prim .requestCommand effArgs rfl) (.cons handle (.cons (.bin .add key (.int 1)) (.cons clo .nil)))
  .lam (.ctor (vs := [[Ty.dsl .effect [.int]], []]) ⟨0, by decide⟩ (.cons req .nil))

def startM : MachineV recordsT .int := { reactM with name := "start", effect := .closed startEffectE }

def startSvc : ServiceV := { querySvc with name := "st", queries := [], machines := [startM] }

def startLayout : Layout :=
  Layout.addTys (fun _ => 3) { effects := [sendKey ⟨"m", 9, 9, 0⟩, sendKey ⟨"m", 3, 7, 0⟩] } (reactTys ++ [.tuple [.int]])

def startsCheck (solver : Solver) : IO Bool := do
  let L := startLayout
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: machine starts: {m}"; return false
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dopt, _) := L.find? (Ty.option (.dsl .effect [.int])) | fail "no effect option"
  let some wf := (SymState.vars 0).wf L (v := startSvc) [] | fail "no wf"
  let some rsrt := L.srt? recordsT | fail "no records sort"
  let some msrt := L.srt? startM.table | fail "no table sort"
  let some psrt := L.srt? (noPending querySvc) | fail "no pending sort"
  let some dts := L.datatypes? | fail "no datatypes"
  match ReactCode.of L startM >>= fun (rc, c0) =>
      (encodeReact L startM rc (.var 5) (.var 0) (.var 1) (.var 6)).bind fun (o, c) =>
        (rankStarts L prelude startM dopt (.var 3) o.starts).map fun S => (S, startCount dopt o.starts, andT c0 c) with
  | .error r => fail s!"no encoding: {repr r}"
  | .ok (S, count, cond) =>
    let Sr := slotsOf dr drt nr 2 (.var 0)
    let goal := [Sr[0]!.1, Sr[1]!.1, .not Sr[2]!.1, .eq (Sr[0]!.2[0]) (.int 5), .eq (Sr[1]!.2[0]) (.int 3),
      .eq (.var 1) (.int 100), .eq (.var 3) (.int 40)]
    let script : Script :=
      { datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt, .int], asserts := wf :: cond :: goal,
        shows := List.range 7 }
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let some s := (SymState.vars 0).decode M L (v := startSvc) prelude [] | fail "the model does not decode"
      let some (.int ev) := vs.lookup 6 | fail "no event"
      let some [⟨m, insts⟩] := some s.machines.toSigma | fail "not one machine"
      let effs := (Step.machineStep (e := startSvc.event) prelude s.records s.now ev m insts).2.zipIdx s.nextId
      -- Each flagged effect slot as (wire id, key, effect value), in slot order.
      let read := S.filterMap fun r => if (r.flag.denote M).toBool then
        match r.id.denote M, r.key.denote M with
        | .int id, .int k => some (id, k, r.effect.denote M)
        | _, _ => none
        else none
      let agrees (got : List (Int × Int × Val)) : Bool :=
        let sorted := got.mergeSort fun a b => a.1 ≤ b.1
        sorted.length == effs.length && (sorted.zip effs).all fun ((id, k, w), ((snd, eff), n)) =>
          id == n && (match snd with | .machine _ ⟨_, kv⟩ => intDen _ kv == some k | _ => false) && effMatches L eff w
      let mut ok := true
      if !agrees read || effs.map (·.2) != [40, 41] then
        ok ← fail s!"the effect slots hold {read.map fun (id, k, _) => (id, k)}, the step {effs.length} effects"
      if count.denote M != .int effs.length then ok ← fail s!"the count is {(count.denote M).print}"
      if agrees (read.zipIdx.map fun ((_, k, w), j) => (40 + j, k, w)) then
        ok ← fail "ids by slot order pass the comparison"
      return ok
    | a => fail s!"{repr a}"

/-! One firing round on a machine's table at the deadline 90, now 100: keys 7 and 3 (slots in that order) both wait
for 90, entering state 1. The least key fires: key 3 enters 1, where `after` starts a timer due at 105 to state 2 and
`effect` requests `send` with 4; key 7 keeps its timer. The decoded table must be `fireFirst` on the instances in key
order, and the start slots flagged must hold `fireFirst`'s one effect, key 3's; firing the first slot (key 7) must
fail both comparisons. -/

def fireCheck (solver : Solver) : IO Bool := do
  let L := startLayout
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: timer round: {m}"; return false
  let some (d, n) := L.find? startM.table | fail "no table"
  let some (dt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no slot"
  let some (de, _) := L.find? (instEntry .int) | fail "no entry"
  let some (dopt, _) := L.find? (Ty.option (.tuple [.int, .int])) | fail "no timer option"
  let some (dp, _) := L.find? (.tuple [.int, .int]) | fail "no timer"
  let some (dxo, _) := L.find? (Ty.option (.dsl .effect [.int])) | fail "no effect option"
  let some wf := (SymState.vars 0).wf L (v := startSvc) [] | fail "no wf"
  let some rsrt := L.srt? recordsT | fail "no records sort"
  let some msrt := L.srt? startM.table | fail "no table sort"
  let some psrt := L.srt? (noPending querySvc) | fail "no pending sort"
  let some dts := L.datatypes? | fail "no datatypes"
  match startM.after.code L >>= fun (af, c0) => startM.effect.code L >>= fun (fx, c1) =>
      (encodeFire L prelude startM af fx (.var 5) (.bool false) (.var 7) (.var 0) (.var 1)).map fun (o, c) =>
        (o, andT c0 (andT c1 c)) with
  | .error r => fail s!"no encoding: {repr r}"
  | .ok (o, cond) =>
    let So := slotsOf d dt n 2 (.var 5)
    let key (j : Nat) := So[j]!.2[0]
    let state (j : Nat) := Term.sel de 0 0 (So[j]!.2[1])
    let timer (j : Nat) := Term.sel de 0 1 (So[j]!.2[1])
    let waits (j : Nat) := [Term.is dopt 0 (timer j), .eq (.sel dp 0 0 (.sel dopt 0 0 (timer j))) (.int 90),
      .eq (.sel dp 0 1 (.sel dopt 0 0 (timer j))) (.int 1)]
    let goal := [So[0]!.1, So[1]!.1, .not So[2]!.1, .eq (key 0) (.int 7), .eq (state 0) (.int 0), .eq (key 1) (.int 3),
      .eq (state 1) (.int 0), .eq (.var 1) (.int 100), .eq (.var 7) (.int 90), .eq (.var 6) o.table] ++ waits 0 ++ waits 1
    let script : Script :=
      { datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt, msrt, .int], asserts := wf :: cond :: goal,
        shows := List.range 8 }
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let some s := (SymState.vars 0).decode M L (v := startSvc) prelude [] | fail "the model does not decode"
      let some tbl := decodeV L startM.table ((Term.var 6).denote M) | fail "the new table does not decode"
      let some tbl0 := decodeV L startM.table ((Term.var 5).denote M) | fail "the old table does not decode"
      let read := instancesOf prelude startM (Ty.down _ startM.table_data tbl)
      let view {r e : Ty} (m : MachineV r e) (is : List (Step.Instance m)) := is.map fun i =>
        (intDen _ i.key, intDen _ i.state, i.timer.map fun (d, st) => (d, intDen _ st))
      let some [⟨m, insts⟩] := some s.machines.toSigma | fail "not one machine"
      let step := Step.fireFirst m s.records s.now 90 insts
      let bySlot := Step.fireFirst startM s.records s.now 90
        ((Ty.down _ startM.table_data tbl0).1.map fun (k, x) => instOf startM k x)
      let starts := o.starts.filterMap fun ⟨f, k, x⟩ =>
        if ((Term.and f (.is dxo 0 x)).denote M).toBool then
          match k.denote M, (Term.sel dxo 0 0 x).denote M with
          | .int kv, w => some (kv, w)
          | _, _ => none
        else none
      let agrees (effs : List (Sender × EffectV .int)) : Bool :=
        starts.length == effs.length && (starts.zip effs).all fun ((k, w), (snd, eff)) =>
          (match snd with | .machine _ ⟨_, kv⟩ => intDen _ kv == some k | _ => false) && effMatches L eff w
      let mut ok := true
      if view startM read != view m step.1 ||
          view m step.1 != [(some 3, some 1, some (105, some 2)), (some 7, some 0, some (90, some 1))] then
        ok ← fail s!"the new table holds {view startM read}, the step {view m step.1}"
      if (view startM bySlot.1).mergeSort (fun a b => decide (a.1.getD 0 ≤ b.1.getD 0)) == view m step.1 then
        ok ← fail "firing the first slot passes the table comparison"
      if !agrees step.2.1 || step.2.1.length != 1 then
        ok ← fail s!"the start slots hold {starts.map (·.1)}, the step {step.2.1.length} effects"
      if agrees bySlot.2.1 then ok ← fail "firing the first slot passes the effect comparison"
      if o.hit.denote M != .bool true then ok ← fail "no slot has the deadline"
      return ok
    | a => fail s!"{repr a}"

/-! An event whose machine starts requests, for `step_encode`: the machine `start` above in a service that
inserts each event's value into its records and lists the external `mail`'s command `send`. The state holds key 3 in
state 0 and one request pending at wire id 2, with next id 40; the event 5 makes key 3 enter 1 and key 5 start, so
both start a `send`. The pending table and next id read from the model must be the step's (the two new requests at 40
for key 3 and 41 for key 5, beside the old one), and the out lines the new requests; the old pending table must not
pass the comparison. With two requests already pending, the three slots cannot take two more: the script is unsat,
and the step really holds four. -/

def wrapIntE : E (.fn [.int] .int) := .lam (.var .here)

def writeSvcOf (m : MachineV recordsT .int) : ServiceV :=
  { insertSvc with name := "w", queries := [], subscribes := [⟨"x", "set", .int, .closed wrapIntE⟩],
                   machines := [m], declared := [("mail", .externalCommand "send" .int Ty.nil Ty.nil)] }

def writeSvc : ServiceV := writeSvcOf startM

def writeSites : List AnySite := Tazuna.Ir.Expr.sites .nil startEffectE

def writeShapesOf (m : MachineV recordsT .int) : List (PendingShape (writeSvcOf m).event) := shapes (writeSvcOf m)

def writeShapes : List (PendingShape writeSvc.event) := writeShapesOf startM

def writeLayoutOf (m : MachineV recordsT .int) (keys : List EffectKey) (slots : Nat) : Layout :=
  Layout.addTys (fun _ => slots) { effects := keys }
    (reactTys ++ [.tuple [.int], pendingTable (writeShapesOf m)] ++ Tazuna.Smt.Expr.tys insertE ++
      Tazuna.Smt.Expr.tys invariantsE ++ Tazuna.Smt.Expr.tys wrapIntE)

def writeLayout (slots : Nat) : Layout := svcLayout writeSvc slots

def writeI : Fin writeSvc.subscribes.length := ⟨0, by decide⟩

/-- v0..v5 the state (v4 the pending table, v5 the instance table), v6 the event value, v7 the new pending table, v8
the next id after, v9 the records after, v10 the new instance table. -/
def writeScriptOf (m : MachineV recordsT .int) (L : Layout) (goal : List Term) :
    Except String (Script × List (Slot 2)) := do
  let v := writeSvcOf m
  let shs := writeShapesOf m
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (o, t) ← eventTerms L writeSites v ⟨0, by simp [v, writeSvcOf]⟩ S (.var 6)
  let d := o.finish.settle.terms.done
  let below ← enc (pendingBelowT L shs S.pending S.nextId)
  let some wf := S.wf L (v := v) shs | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable shs) | throw "no pending sort"
  let some msrt := L.srt? m.table | throw "no table sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [tbl] := d.tables.toList | throw "not one machine"
  let some (dp, n) := L.find? (pendingTable shs) | throw "no pending table"
  let some (dt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry shs]) | throw "no pending slot"
  pure ({ datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt, .int, psrt, .int, rsrt, msrt],
          asserts := [wf, below, t.codes, t.sites, t.cond, .eq (.var 7) o.finish.pending, .eq (.var 8) d.nextId,
            .eq (.var 9) d.records, .eq (.var 10) tbl] ++ goal,
          shows := List.range 11 }, slotsOf dp dt n 2 (.var 4))

def writeScript (slots : Nat) (goal : List Term) : Except String (Script × List (Slot 2)) :=
  writeScriptOf startM (writeLayout slots) goal

/-- What the comparison reads of a pending request: id, external, name, the sender's key and the input. -/
def pendView (p : Step.Pending writeSvc.event) : Nat × String × String × Option Int × Option Int :=
  (p.id, p.external, p.request.name, (match p.sender with | .machine _ ⟨t, k⟩ => intDen t k | _ => none),
    intDen p.request.input p.request.value)

def writeCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: event writes requests: {m}"; return false
  let L := writeLayout 3
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dm, nm) := L.find? startM.table | fail "no instance table"
  let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no instance slot"
  let some (de, _) := L.find? (instEntry .int) | fail "no instance entry"
  let Sr := slotsOf dr drt nr 2 (.var 0)
  let Sm := slotsOf dm dmt nm 2 (.var 5)
  let state (Sp : List (Slot 2)) (pend : List Term) := [Sr[0]!.1, .not Sr[1]!.1, .not Sr[2]!.1,
    .eq (Sr[0]!.2[0]) (.int 3), Sm[0]!.1, .not Sm[1]!.1, .not Sm[2]!.1, .eq (Sm[0]!.2[0]) (.int 3),
    .eq (Term.sel de 0 0 (Sm[0]!.2[1])) (.int 0), .eq (.var 6) (.int 5), .eq (.var 3) (.int 40)] ++
    pend.zipIdx.map (fun (id, j) => .and Sp[j]!.1 (.eq (Sp[j]!.2[0]) id)) ++
    (List.range (3 - pend.length)).map fun j => .not Sp[pend.length + j]!.1
  match writeScript 3 [] with
  | .error m => fail m
  | .ok (_, Sp) =>
    let mut ok := true
    match writeScript 3 (state Sp [.int 2]) with
    | .error m => ok ← fail m
    | .ok (script, _) =>
      match ← solver.run script with
      | .sat vs =>
        let M := modelOf vs
        match (SymState.vars 0).decode M L (v := writeSvc) prelude writeShapes,
            (SymInput.event (shs := []) (slots := 0) writeI (.var 6)).decode M L (v := writeSvc) rfl,
            decodePending L writeShapes ((Term.var 7).denote M), (vs.lookup 8) with
        | some s, some x, some pend', some (.int n') =>
          let r := step prelude writeSvc s x
          let sorted (ps : List (Step.Pending writeSvc.event)) := (ps.map pendView).mergeSort fun a b => a.1 ≤ b.1
          let outs := (r.out.map fun l => (l.id, l.external, l.name)).mergeSort fun a b => a.1 ≤ b.1
          let newOnes := (sorted pend').filter (·.1 ≥ s.nextId) |>.map fun (id, x, nm, _, _) => (id, x, nm)
          if r.outcome.summary != "accepted" then ok ← fail s!"the step says {r.outcome.summary}"
          if sorted pend' != sorted r.state.pending || n' != r.state.nextId then
            ok ← fail s!"the model's pending table holds {sorted pend'} and next id {n'}, the step {sorted r.state.pending} and {r.state.nextId}"
          if outs != newOnes then ok ← fail s!"the out lines are {outs}, the new entries {newOnes}"
          if (sorted pend').map (·.1) != [2, 40, 41] then ok ← fail s!"the wire ids are {(sorted pend').map (·.1)}"
          if sorted pend' == sorted s.pending then ok ← fail "the old pending table passes the comparison"
        | _, _, _, _ => ok ← fail "the model does not decode"
      | a => ok ← fail s!"{repr a}"
    match writeScript 3 (state Sp [.int 1, .int 2]) with
    | .error m => ok ← fail m
    | .ok (script, _) =>
      match ← solver.run script with
      | .unsat => pure ()
      | a => ok ← fail s!"two pending and two new requests in three slots, yet the script is {repr a}"
    return ok

/-! An event step that can write no request although requests have pending shapes: the service `w` with the
machine `react` whose effect builds an `on_answer` closure but starts nothing, and a layout that names no effect
kind, as when the program builds an `on_answer` closure but never a request. The script must be well-sorted and sat, and the pending table and next id read
from the model must be the step's: the one request already pending, next id 40. -/

/-- `react` with an effect whose source builds `send`'s `on_answer` closure but starts nothing: the service can hold
requests of that shape, yet the machine writes none. -/
def quietM : MachineV recordsT .int :=
  let key : Expr [] [invCtxT] .int := .field (ft := .int) "key" 0 (by simp) (.var .here)
  let body : Expr [] [.int] answerTyE := .lam (.list (.cons (.var (.there .here)) .nil))
  { reactM with effect := .closed (.lam (.let_ (.close ⟨"m", 3, 7, 0⟩ (.cons key .nil) rfl rfl body)
      (.ctor (vs := [[Ty.dsl .effect [.int]], []]) ⟨1, by decide⟩ .nil))) }

def quietCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: no effect kinds: {m}"; return false
  let L := writeLayoutOf quietM [] 3
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dm, nm) := L.find? quietM.table | fail "no instance table"
  let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no instance slot"
  let Sr := slotsOf dr drt nr 2 (.var 0)
  let Sm := slotsOf dm dmt nm 2 (.var 5)
  match writeScriptOf quietM (writeLayoutOf quietM [] 3) [] with
  | .error m => fail m
  | .ok (_, Sp) =>
    let goal := [Sr[0]!.1, .not Sr[1]!.1, .not Sr[2]!.1, .eq (Sr[0]!.2[0]) (.int 3), .not Sm[0]!.1,
      .not Sm[1]!.1, .not Sm[2]!.1, .eq (.var 6) (.int 5), .eq (.var 3) (.int 40), Sp[0]!.1,
      .eq (Sp[0]!.2[0]) (.int 2), .not Sp[1]!.1, .not Sp[2]!.1]
    match writeScriptOf quietM (writeLayoutOf quietM [] 3) goal with
    | .error m => fail m
    | .ok (script, _) =>
      match ← solver.run script with
      | .sat vs =>
        let M := modelOf vs
        match (SymState.vars 0).decode M L (v := writeSvcOf quietM) prelude (writeShapesOf quietM),
            decodePending L (writeShapesOf quietM) ((Term.var 7).denote M), vs.lookup 8 with
        | some s, some pend', some (.int n') =>
          let r := step prelude (writeSvcOf quietM) s (.event ⟨0, by simp [writeSvcOf]⟩ (by exact (5 : Int)))
          let ids (ps : List (Step.Pending (writeSvcOf quietM).event)) := (ps.map (·.id)).mergeSort (· ≤ ·)
          if r.outcome.summary != "accepted" then return ← fail s!"the step says {r.outcome.summary}"
          if ids pend' != ids r.state.pending || n' != r.state.nextId || ids pend' != [2] then
            return ← fail s!"the model's pending ids are {ids pend'} and next id {n'}, the step's {ids r.state.pending} and {r.state.nextId}"
          return true
        | _, _, _ => fail "the model does not decode"
      | a => fail s!"{repr a}"

/-! An event whose machine and reaction start requests, for `step_encode`: the service `w` above with the
reaction `fan`, which requests `send` with the event's value plus 1 and plus 2, in that order. From the state of
`event writes requests` (key 3 in state 0, request 2 pending, next id 40) the event 5 starts the machine's two
requests at 40 (key 3) and 41 (key 5), then the reaction's at 42 (input 6) and 43 (input 7). The pending table and
next id read from the model must be the step's, and swapping the reaction's two ids must not pass the comparison.
The reaction's `on_answer` is a site of its own, so each sender has one pending shape and its entries skip the
other's kind. With 4 pending slots, one pending and four new requests do not fit: the script is unsat. -/

def fanSendE (k : Int) : Expr [] [Ty.reactionCtx recordsT, .int] (.dsl .effect [.int]) :=
  let ev : Expr [] [Ty.reactionCtx recordsT, .int] .int := .var (.there .here)
  let handle : Expr [] [Ty.reactionCtx recordsT, .int] (.dsl .externalCommand [.int, Ty.nil, Ty.nil]) :=
    .call (.prim .externalCommand [.int, Ty.nil, Ty.nil] rfl) (.cons (.str "send") .nil)
  let body : Expr [] [.int] answerTyE := .lam (.list (.cons (.var (.there .here)) .nil))
  let clo : Expr [] [Ty.reactionCtx recordsT, .int] (.dsl .closure [answerTyE]) :=
    .close ⟨"m", 4, 1, 0⟩ (.cons ev .nil) rfl rfl body
  .call (.prim .requestCommand effArgs rfl) (.cons handle (.cons (.bin .add ev (.int k)) (.cons clo .nil)))

def fanE : Expr [] [] (.fn [Ty.reactionCtx recordsT, .int] (.list (.dsl .effect [.int]))) :=
  .lam (.list (.cons (fanSendE 1) (.cons (fanSendE 2) .nil)))

def fanR : ReactionV recordsT .int := ⟨"fan", .closed fanE⟩

def fanSvc : ServiceV := { writeSvc with name := "f", reactions := [fanR] }

def fanShapes : List (PendingShape fanSvc.event) := shapes fanSvc

def fanLayout (slots : Nat) : Layout :=
  Layout.addTys (fun _ => slots) { effects := [sendKey ⟨"m", 3, 7, 0⟩, sendKey ⟨"m", 4, 1, 0⟩] }
    (reactTys ++ [.tuple [.int], .tuple [], pendingTable fanShapes] ++ Tazuna.Smt.Expr.tys insertE ++
      Tazuna.Smt.Expr.tys invariantsE ++ Tazuna.Smt.Expr.tys wrapIntE ++ Tazuna.Smt.Expr.tys fanE)

def fanI : Fin fanSvc.subscribes.length := ⟨0, by decide⟩

/-- v0..v5 the state (v4 the pending table, v5 the instance table), v6 the event value, v7 the new pending table, v8
the next id after. -/
def fanScript (slots : Nat) (goal : List Term) : Except String (Script × List (Slot 2)) := do
  let L := fanLayout slots
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (o, t) ← eventTerms L writeSites fanSvc fanI S (.var 6)
  let below ← enc (pendingBelowT L fanShapes S.pending S.nextId)
  let some wf := S.wf L (v := fanSvc) fanShapes | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable fanShapes) | throw "no pending sort"
  let some msrt := L.srt? startM.table | throw "no table sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let some (d, n) := L.find? (pendingTable fanShapes) | throw "no pending table"
  let some (dt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry fanShapes]) | throw "no pending slot"
  pure ({ datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt, .int, psrt, .int],
          asserts := [wf, below, t.codes, t.sites, t.cond, .eq (.var 7) o.finish.pending,
            .eq (.var 8) o.finish.settle.terms.done.nextId] ++ goal,
          shows := List.range 9 }, slotsOf d dt n 2 (.var 4))

def fanCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: reactions write requests: {m}"; return false
  let state (slots : Nat) (Sp : List (Slot 2)) : List Term :=
    let L := fanLayout slots
    match L.find? recordsT, L.find? (.tuple [Ty.bool, .int, .int]), L.find? startM.table,
        L.find? (.tuple [Ty.bool, .int, instEntry .int]), L.find? (instEntry .int) with
    | some (dr, nr), some (drt, _), some (dm, nm), some (dmt, _), some (de, _) =>
      let Sr := slotsOf dr drt nr 2 (.var 0)
      let Sm := slotsOf dm dmt nm 2 (.var 5)
      [Sr[0]!.1, .eq (Sr[0]!.2[0]) (.int 3), Sm[0]!.1, .eq (Sm[0]!.2[0]) (.int 3),
        .eq (Term.sel de 0 0 (Sm[0]!.2[1])) (.int 0), .eq (.var 6) (.int 5), .eq (.var 3) (.int 40),
        Sp[0]!.1, .eq (Sp[0]!.2[0]) (.int 2)] ++
        ((List.range (slots - 1)).flatMap fun j => [.not Sr[j + 1]!.1, .not Sm[j + 1]!.1, .not Sp[j + 1]!.1])
    | _, _, _, _, _ => [.bool false]
  let mut ok := true
  match fanScript 5 [] with
  | .error m => ok ← fail m
  | .ok (_, Sp) =>
    match fanScript 5 (state 5 Sp) with
    | .error m => ok ← fail m
    | .ok (script, _) =>
      match ← solver.run script with
      | .sat vs =>
        let M := modelOf vs
        let L := fanLayout 5
        match (SymState.vars 0).decode M L (v := fanSvc) prelude fanShapes,
            (SymInput.event (shs := []) (slots := 0) fanI (.var 6)).decode M L (v := fanSvc) rfl,
            decodePending L fanShapes ((Term.var 7).denote M), (vs.lookup 8) with
        | some s, some x, some pend', some (.int n') =>
          let r := step prelude fanSvc s x
          let view (p : Step.Pending fanSvc.event) : Nat × Option Int :=
            (p.id, intDen p.request.input p.request.value)
          let sorted (ps : List (Step.Pending fanSvc.event)) := (ps.map view).mergeSort fun a b => a.1 ≤ b.1
          let outs := (r.out.map (·.id)).mergeSort (· ≤ ·)
          let swapped := (sorted pend').map fun (id, i) => (if id == 42 then 43 else if id == 43 then 42 else id, i)
          if r.outcome.summary != "accepted" then ok ← fail s!"the step says {r.outcome.summary}"
          if sorted pend' != sorted r.state.pending || n' != r.state.nextId then
            ok ← fail s!"the model's pending table holds {sorted pend'} and next id {n'}, the step {sorted r.state.pending} and {r.state.nextId}"
          if outs != ((sorted pend').map (·.1)).filter (· ≥ 40) then ok ← fail s!"the out lines are {outs}"
          if (sorted pend').filter (·.1 ≥ 42) != [(42, some 6), (43, some 7)] then
            ok ← fail s!"the reaction's requests are {(sorted pend').filter (·.1 ≥ 42)}"
          if (swapped.mergeSort fun a b => a.1 ≤ b.1) == sorted r.state.pending then
            ok ← fail "the reaction's ids swapped pass the comparison"
        | _, _, _, _ => ok ← fail "the model does not decode"
      | a => ok ← fail s!"{repr a}"
  match fanScript 4 [] with
  | .error m => ok ← fail m
  | .ok (_, Sp) =>
    match fanScript 4 (state 4 Sp) with
    | .error m => ok ← fail m
    | .ok (script, _) =>
      match ← solver.run script with
      | .unsat => pure ()
      | a => ok ← fail s!"one pending and four new requests in four slots, yet the script is {repr a}"
  return ok

/-! A clock line with timers, for `step_encode`: the service `w` above with the cascade bound `cascade`. Key 7
waits for 80 and key 3 for 90, both entering state 1, which starts a timer due at now + 5 and requests `send`. The
state holds one request pending at wire id 2, next id 40, now 50; the line's time is 100. Round one fires key 7 (the
earliest deadline, though key 3 is smaller), round two key 3, and round three finds no due timer. With cascade 2 the
step is accepted: the decoded pending table, next id and instance table must be the step's (key 7's request at 40,
key 3's at 41), and ids by key order must not pass the comparison. With cascade 1 both rounds use the bound, so the
script must say the bound is exceeded and the step must be the cascade fault. -/

def clockFireSvc (cascade : Int) : ServiceV := { writeSvc with name := "k", bounds := ⟨[], 0, cascade, 0⟩ }

def clockShapes (cascade : Int) : List (PendingShape (clockFireSvc cascade).event) :=
  shapes (clockFireSvc cascade)

/-- v0..v5 the state (v4 the pending table, v5 the instance table), v6 the line's time, v7 the new pending table, v8
the next id after, v9 the new instance table. -/
def clockFireScript (cascade : Int) (slots : Nat) (goal : List Term) :
    Except String (Script × ClockOut (clockFireSvc cascade)) := do
  let v := clockFireSvc cascade
  let L := writeLayout slots
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let t ← stepOf L writeSites v S (fun _ => pure (.clock (.var 6)))
  let .clock o := t.out | throw "not a clock line's terms"
  let below ← enc (pendingBelowT L (clockShapes cascade) S.pending S.nextId)
  let some wf := S.wf L (v := v) (clockShapes cascade) | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable (clockShapes cascade)) | throw "no pending sort"
  let some msrt := L.srt? startM.table | throw "no table sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [tbl] := o.finish.settle.terms.done.tables.toList | throw "not one machine"
  pure ({ datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt, .int, psrt, .int, msrt],
          asserts := [wf, below, t.codes, t.sites, t.cond, .eq (.var 7) o.finish.pending,
            .eq (.var 8) o.finish.settle.terms.done.nextId, .eq (.var 9) tbl] ++ goal,
          shows := List.range 10 }, o)

def clockFireCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: clock fires timers: {m}"; return false
  let L := writeLayout 3
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dm, nm) := L.find? startM.table | fail "no instance table"
  let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no instance slot"
  let some (de, _) := L.find? (instEntry .int) | fail "no instance entry"
  let some (dto, _) := L.find? (Ty.option (.tuple [.int, .int])) | fail "no timer option"
  let some (dp, _) := L.find? (.tuple [.int, .int]) | fail "no timer"
  let some (d, n) := L.find? (pendingTable (clockShapes 2)) | fail "no pending table"
  let some (dt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry (clockShapes 2)]) | fail "no pending slot"
  let Sr := slotsOf dr drt nr 2 (.var 0)
  let Sm := slotsOf dm dmt nm 2 (.var 5)
  let Sp := slotsOf d dt n 2 (.var 4)
  let waits (j : Nat) (key dl : Int) := [Sm[j]!.1, .eq (Sm[j]!.2[0]) (.int key),
    .eq (Term.sel de 0 0 (Sm[j]!.2[1])) (.int 0), .is dto 0 (Term.sel de 0 1 (Sm[j]!.2[1])),
    .eq (.sel dp 0 0 (.sel dto 0 0 (Term.sel de 0 1 (Sm[j]!.2[1])))) (.int dl),
    .eq (.sel dp 0 1 (.sel dto 0 0 (Term.sel de 0 1 (Sm[j]!.2[1])))) (.int 1)]
  let goal := [Sr[0]!.1, .not Sr[1]!.1, .not Sr[2]!.1, .eq (Sr[0]!.2[0]) (.int 3), .not Sm[2]!.1,
    .eq (.var 1) (.int 50), .eq (.var 6) (.int 100), .eq (.var 3) (.int 40), Sp[0]!.1, .eq (Sp[0]!.2[0]) (.int 2),
    .not Sp[1]!.1, .not Sp[2]!.1] ++ waits 0 7 80 ++ waits 1 3 90
  let view {r e : Ty} (m : MachineV r e) (is : List (Step.Instance m)) := is.map fun i =>
    (intDen _ i.key, intDen _ i.state, i.timer.map fun (d, st) => (d, intDen _ st))
  let mut ok := true
  match clockFireScript 2 3 goal with
  | .error m => ok ← fail m
  | .ok (script, o) =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      match (SymState.vars 0).decode M L (v := clockFireSvc 2) prelude (clockShapes 2),
          decodePending L (clockShapes 2) ((Term.var 7).denote M), vs.lookup 8,
          decodeV L startM.table ((Term.var 9).denote M) with
      | some s, some pend', some (.int n'), some tbl =>
        let r := step prelude (clockFireSvc 2) s (.clock 100)
        let sorted (ps : List (Step.Pending writeSvc.event)) := (ps.map pendView).mergeSort fun a b => a.1 ≤ b.1
        let outs := (r.out.map fun l => (l.id, l.external, l.name)).mergeSort fun a b => a.1 ≤ b.1
        let newOnes := (sorted pend').filter (·.1 ≥ s.nextId) |>.map fun (id, x, nm, _, _) => (id, x, nm)
        let read := view startM (instancesOf prelude startM (Ty.down _ startM.table_data tbl))
        let stepTable := match r.state.machines.toSigma with
          | [⟨m, insts⟩] => view m insts
          | _ => []
        let keyOrder := (sorted pend').map fun (id, x, nm, k, i) =>
          (if id ≥ 40 then (if k == some 3 then 40 else 41) else id, x, nm, k, i)
        if r.outcome.summary != "accepted" then ok ← fail s!"the step says {r.outcome.summary}"
        if (o.over.denote M).toBool then ok ← fail "the script says the bound is exceeded"
        if sorted pend' != sorted r.state.pending || n' != r.state.nextId then
          ok ← fail s!"the model's pending table holds {sorted pend'} and next id {n'}, the step {sorted r.state.pending} and {r.state.nextId}"
        if outs != newOnes then ok ← fail s!"the out lines are {outs}, the new entries {newOnes}"
        let ids := (sorted pend').map fun (id, _, _, k, _) => (id, if id ≥ 40 then k else none)
        if ids != [(2, none), (40, some 7), (41, some 3)] then ok ← fail s!"the wire ids are {ids}"
        if read != stepTable then ok ← fail s!"the new table holds {read}, the step {stepTable}"
        if keyOrder == sorted r.state.pending then ok ← fail "ids by key order pass the comparison"
      | _, _, _, _ => ok ← fail "the model does not decode"
    | a => ok ← fail s!"{repr a}"
  match clockFireScript 1 3 goal with
  | .error m => ok ← fail m
  | .ok (script, o) =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      match (SymState.vars 0).decode M L (v := clockFireSvc 1) prelude (clockShapes 1) with
      | some s =>
        let r := step prelude (clockFireSvc 1) s (.clock 100)
        if !(o.over.denote M).toBool then ok ← fail "with cascade 1 the script does not say the bound is exceeded"
        if r.outcome.summary != "fault cascadeLimit" then ok ← fail s!"with cascade 1 the step says {r.outcome.summary}"
      | none => ok ← fail "the model does not decode"
    | a => ok ← fail s!"cascade 1: {repr a}"
  return ok

/-! A list of effects where no effect kind exists, as a reaction of a service that requests nothing returns: the
list has no slots, so the solver's list is empty, as eval's `[]` is, and a script that asserts an occupied slot cannot
be written (the comparison against a one-item list fails). -/

def noEffectsE : Expr [] [] (.list (.dsl .effect [.int])) := .list .nil

def noEffectsCheck (solver : Solver) : IO Bool := do
  let L := Layout.addTys (fun _ => 2) {} [.list (.dsl .effect [.int])]
  let some (_, n) := L.find? (.list (.dsl .effect [.int])) | IO.println "smt-check: no effects: no list"; return false
  if n != 0 then IO.println s!"smt-check: no effects: the list has {n} slots"; return false
  let some srt := L.srt? (.list (.dsl .effect [.int])) | IO.println "smt-check: no effects: no sort"; return false
  let some dts := L.datatypes? | IO.println "smt-check: no effects: no datatypes"; return false
  match encode L (G := []) () noEffectsE () with
  | .error r => IO.println s!"smt-check: no effects: no encoding: {repr r}"; return false
  | .ok (code, cond) =>
    match ← solver.run { datatypes := dts, vars := [srt], asserts := [.eq (.var 0) code, cond], shows := [0] } with
    | .sat vs =>
      let some v := vs.lookup 0 | IO.println "smt-check: no effects: no value"; return false
      let agrees (want : Nat) : Bool := (occupied v).length == want
      if !agrees (noEffectsE.eval (G := []) .nil () ()).length then
        IO.println s!"smt-check: no effects: the solver's {v.print} is not empty"; return false
      if agrees 1 then IO.println "smt-check: no effects: the comparison accepts one effect"; return false
      return true
    | a => IO.println s!"smt-check: no effects: {repr a}"; return false

/-! A list of events in one step, for `events_encode`: the service `w` above, whose events insert their value as a
key and whose machine `start` keeps one instance per key, starts it at 0, enters 1 on any later event (with a timer
due at now + 5) and requests `send` on entering a state. From no records and no instances, at now 100 and next id 40
with request 2 pending, the events 3 and 3 run (the list's free third slot holds 9, which must start nothing): the first starts key 3 at 0 (request at 40), the second finds that
instance and enters 1 (request at 41). The records, instance table, pending table and next id read from the model
must be what `applyEvents` leaves; the second event reacting on the instance tables from before the first (key 3
starting afresh) must not pass the comparison. -/

/-- The service `w`'s layout, in a program that also writes a list literal of `slots` Ints, as a `decide` returning
that many events would: the list's slots are its longest literal. -/
def eventsLayout (slots : Nat) : Layout := svcLayout writeSvc slots ⟨[], [], [], [(.list .int, slots)]⟩

/-- v0..v5 the state (v4 the pending table, v5 the instance table), v6 the event list, v7 the new pending table, v8
the next id after, v9 the records after, v10 the new instance table. -/
def eventsScript (slots : Nat) (goal : List Term) : Except String (Script × List (Slot 2) × List (Slot 1)) := do
  let L := eventsLayout slots
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (apply, ca) ← enc (writeSvc.apply.code L)
  let (dl, nl, dlt) ← enc (collD L (.list .int) [.int])
  let senv ← enc (StepEnv.of L writeShapes)
  let (o, c) ← enc (encodeEvents L prelude writeSvc writeShapes senv apply S.now (slotsOf dl dlt nl 1 (.var 6))
    S.records S.machines S.nextId (.int 0))
  let (pT, cp) ← enc (encodePending L writeShapes S.pending o.news)
  let below ← enc (pendingBelowT L writeShapes S.pending S.nextId)
  let some wf := S.wf L (v := writeSvc) writeShapes | throw "no well-formedness"
  let some wfl := wfT L (.list .int) (.var 6) | throw "no list well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable writeShapes) | throw "no pending sort"
  let some msrt := L.srt? startM.table | throw "no table sort"
  let some lsrt := L.srt? (.list .int) | throw "no list sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [tbl] := o.tables.toList | throw "not one machine"
  let some (d, n) := L.find? (pendingTable writeShapes) | throw "no pending table"
  let some (dt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry writeShapes]) | throw "no pending slot"
  pure ({ datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt, lsrt, psrt, .int, rsrt, msrt],
          asserts := [wf, wfl, below, ca, c, cp, .eq (.var 7) pT, .eq (.var 8) o.nextId, .eq (.var 9) o.records,
            .eq (.var 10) tbl] ++ goal,
          shows := List.range 11 }, slotsOf d dt n 2 (.var 4), slotsOf dl dlt nl 1 (.var 6))

def eventsCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: a list of events: {m}"; return false
  let L := eventsLayout 3
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dm, nm) := L.find? startM.table | fail "no instance table"
  let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no instance slot"
  let Sr := slotsOf dr drt nr 2 (.var 0)
  let Sm := slotsOf dm dmt nm 2 (.var 5)
  match eventsScript 3 [] with
  | .error m => fail m
  | .ok (_, Sp, Se) =>
    let goal := [.not Sr[0]!.1, .not Sr[1]!.1, .not Sr[2]!.1, .not Sm[0]!.1, .not Sm[1]!.1, .not Sm[2]!.1,
      Sp[0]!.1, .eq (Sp[0]!.2[0]) (.int 2), .not Sp[1]!.1, .not Sp[2]!.1, .eq (.var 1) (.int 100),
      .eq (.var 3) (.int 40), Se[0]!.1, .eq (Se[0]!.2[0]) (.int 3), Se[1]!.1, .eq (Se[1]!.2[0]) (.int 3),
      .not Se[2]!.1, .eq (Se[2]!.2[0]) (.int 9)]
    match eventsScript 3 goal with
    | .error m => fail m
    | .ok (script, _, _) =>
      match ← solver.run script with
      | .sat vs =>
        let M := modelOf vs
        let after : SymState writeSvc := { records := .var 9, now := .var 1, fresh := .var 2, nextId := .var 8,
                                           pending := .var 7, machines := .cons (.var 10) .nil }
        match (SymState.vars 0).decode M L (v := writeSvc) prelude writeShapes,
            after.decode M L (v := writeSvc) prelude writeShapes, (vs.lookup 6).bind (decodeV L (.list .int)) with
        | some s, some s', some evs =>
          let evs : List Int := Ty.down (.list .int) rfl evs
          let view (sms : List (Step.MachineState writeSvc.records writeSvc.event)) :=
            sms.map fun ⟨_, is⟩ => is.map fun i => (intDen _ i.key, intDen _ i.state, i.timer.map fun (d, st) => (d, intDen _ st))
          let sorted (ps : List (Step.Pending writeSvc.event)) := (ps.map pendView).mergeSort fun a b => a.1 ≤ b.1
          match Step.applyEvents prelude ({ state := s } : Step.Acc writeSvc) evs,
              Step.applyEvents prelude ({ state := { s with records := writeSvc.apply.fn (s.records, (3 : Int), ()) } } :
                Step.Acc writeSvc) [(3 : Int)] with
          | .ok a, .ok b =>
            let mut ok := true
            if !sameAs L recordsT rfl a.state.records (vs.lookup 9) then ok ← fail "the records differ from the step's"
            if view s'.machines.toSigma != view a.state.machines.toSigma || view s'.machines.toSigma != [[(some 3, some 1, some (105, some 2))]] then
              ok ← fail s!"the new table holds {view s'.machines.toSigma}, the step {view a.state.machines.toSigma}"
            if sorted s'.pending != sorted a.state.pending || s'.nextId != a.state.nextId then
              ok ← fail s!"the model's pending table holds {sorted s'.pending} and next id {s'.nextId}, the step {sorted a.state.pending} and {a.state.nextId}"
            if (sorted s'.pending).map (·.1) != [2, 40, 41] then ok ← fail s!"the wire ids are {(sorted s'.pending).map (·.1)}"
            if view s'.machines.toSigma == view b.state.machines.toSigma then
              ok ← fail "the second event reacting on the tables from before the first passes the comparison"
            return ok
          | _, _ => fail "the step faults"
        | _, _, _ => fail "the model does not decode"
      | a => fail s!"{repr a}"

/-! A command whose events reach machines, for `step_encode`: the service `w` above with the command `twice`, whose
`decide` accepts any positive input with the events [input, input]. From the state of `a list of events` (no records,
no instances, request 2 pending, next id 40, now 100), alice's `twice 3` applies 3 twice: the first starts key 3 at
0 (request at 40), the second enters 1 (request at 41). The step must be accepted, and the records, instance table,
pending table and next id read from the model must be its own; applying only the first event must not pass the
comparison. -/

def twiceDecideE : E (.fn [cctxT] (Ty.result (.list .int) .str)) :=
  .lam (.ctor (vs := [[.list .int], [.str]]) ⟨0, by decide⟩ (.cons (.list (.cons inputOf (.cons inputOf .nil))) .nil))

def twiceC : CommandV recordsT .int .str :=
  { name := "twice", input := .int, rejection := .str, callers := ["alice"], accepts := .closed acceptsE,
    decide := .closed twiceDecideE, ensures := .closed (.lam (.list .nil)) }

def twiceSvc : ServiceV := { writeSvc with name := "t", commands := [twiceC] }

def twiceShapes : List (PendingShape twiceSvc.event) := shapes twiceSvc

def twiceLayoutOf (slots : Nat) : Layout := svcLayout twiceSvc slots

/-- v0..v5 the state (v4 the pending table, v5 the instance table), v6 the caller, v7 the input, v8 the new pending
table, v9 the next id after, v10 the records after, v11 the new instance table. -/
def twiceScriptOf (slots : Nat) (goal : List Term) : Except String (Script × List (Slot 2)) := do
  let L := twiceLayoutOf slots
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let t ← stepOf L writeSites twiceSvc S (fun _ => pure (.command ⟨0, by decide⟩ (.var 6) (.var 7)))
  let .command o := t.out | throw "not a command's terms"
  let below ← enc (pendingBelowT L twiceShapes S.pending S.nextId)
  let some wf := S.wf L (v := twiceSvc) twiceShapes | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable twiceShapes) | throw "no pending sort"
  let some msrt := L.srt? startM.table | throw "no table sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let d := o.finish.settle.terms.done
  let [tbl] := d.tables.toList | throw "not one machine"
  let some (dp, n) := L.find? (pendingTable twiceShapes) | throw "no pending table"
  let some (dt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry twiceShapes]) | throw "no pending slot"
  pure ({ datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt, .str, .int, psrt, .int, rsrt, msrt],
          asserts := [wf, below, t.codes, t.sites, t.cond, .eq (.var 8) o.finish.pending, .eq (.var 9) d.nextId,
            .eq (.var 10) d.records, .eq (.var 11) tbl] ++ goal,
          shows := List.range 12 }, slotsOf dp dt n 2 (.var 4))

def twiceLayout : Layout := twiceLayoutOf 3

def twiceScript (goal : List Term) : Except String (Script × List (Slot 2)) := twiceScriptOf 3 goal

def twiceCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: a command's events reach machines: {m}"; return false
  let L := twiceLayout
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dm, nm) := L.find? startM.table | fail "no instance table"
  let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no instance slot"
  let Sr := slotsOf dr drt nr 2 (.var 0)
  let Sm := slotsOf dm dmt nm 2 (.var 5)
  match twiceScript [] with
  | .error m => fail m
  | .ok (_, Sp) =>
    let goal := [.not Sr[0]!.1, .not Sr[1]!.1, .not Sr[2]!.1, .not Sm[0]!.1, .not Sm[1]!.1, .not Sm[2]!.1,
      Sp[0]!.1, .eq (Sp[0]!.2[0]) (.int 2), .not Sp[1]!.1, .not Sp[2]!.1, .eq (.var 1) (.int 100),
      .eq (.var 3) (.int 40), .eq (.var 6) (.str "alice"), .eq (.var 7) (.int 3)]
    match twiceScript goal with
    | .error m => fail m
    | .ok (script, _) =>
      match ← solver.run script with
      | .sat vs =>
        let M := modelOf vs
        let after : SymState twiceSvc := { records := .var 10, now := .var 1, fresh := .var 2, nextId := .var 9,
                                           pending := .var 8, machines := .cons (.var 11) .nil }
        match (SymState.vars 0).decode M L (v := twiceSvc) prelude twiceShapes,
            after.decode M L (v := twiceSvc) prelude twiceShapes with
        | some s, some s' =>
          let r := step prelude twiceSvc s (.command ⟨0, by decide⟩ ("alice" : String) (3 : Int))
          let view (sms : List (Step.MachineState twiceSvc.records twiceSvc.event)) :=
            sms.map fun ⟨_, is⟩ => is.map fun i => (intDen _ i.key, intDen _ i.state, i.timer.map fun (d, st) => (d, intDen _ st))
          let ids (ps : List (Step.Pending twiceSvc.event)) := (ps.map (·.id)).mergeSort (· ≤ ·)
          let mut ok := true
          if r.outcome.summary != "accepted" then ok ← fail s!"the step says {r.outcome.summary}"
          if !sameAs L recordsT rfl r.state.records (vs.lookup 10) then ok ← fail "the records differ from the step's"
          if view s'.machines.toSigma != view r.state.machines.toSigma || view s'.machines.toSigma != [[(some 3, some 1, some (105, some 2))]] then
            ok ← fail s!"the new table holds {view s'.machines.toSigma}, the step {view r.state.machines.toSigma}"
          if ids s'.pending != ids r.state.pending || s'.nextId != r.state.nextId || ids s'.pending != [2, 40, 41] then
            ok ← fail s!"the model's pending ids are {ids s'.pending} and next id {s'.nextId}, the step's {ids r.state.pending} and {r.state.nextId}"
          match Step.applyEvents prelude ({ state := s } : Step.Acc twiceSvc) [(3 : Int)] with
          | .ok b => if view s'.machines.toSigma == view b.state.machines.toSigma then ok ← fail "applying only the first event passes the comparison"
          | .error _ => ok ← fail "one event faults"
          return ok
        | _, _ => fail "the model does not decode"
      | a => fail s!"{repr a}"

/-! An answer whose events reach machines, for `step_encode`: the service `w` above, with key 3 in the records and its
instance in state 0, at now 100 and next id 40. Request 2 in slot 0 is the instance's `send`, whose `on_answer`
captured key 3. The answer Ok to 2 makes `on_answer` return [3]; applying 3 lets the instance enter 1 (timer due at
105) and request `send` again at id 40, and request 2 leaves the table. The records, instance table, pending table
and next id read from the model must be the step's; the table before the machine reacts must not pass the
comparison. -/

def answerMLayoutOf (slots : Nat) : Layout := svcLayout writeSvc slots

/-- v0..v5 the state (v4 the pending table, v5 the instance table), v6 the answer, v7 the new pending table, v8 the
next id after, v9 the records after, v10 the new instance table. -/
def answerMScriptOf (slots : Nat) (goal : List Term) : Except String (Script × Term) := do
  let L := answerMLayoutOf slots
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let t ← stepOf L writeSites writeSvc S (answerAt 0 0 (.int 2) (.var 6))
  let .answer o := t.out | throw "not an answer's terms"
  let below ← enc (pendingBelowT L writeShapes S.pending S.nextId)
  let some wf := S.wf L (v := writeSvc) writeShapes | throw "no well-formedness"
  let some wfa := wfT L (answerTy Ty.nil Ty.nil) (.var 6) | throw "no answer well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable writeShapes) | throw "no pending sort"
  let some msrt := L.srt? startM.table | throw "no table sort"
  let some asrt := L.srt? (answerTy Ty.nil Ty.nil) | throw "no answer sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let d := o.finish.settle.terms.done
  let [tbl] := d.tables.toList | throw "not one machine"
  pure ({ datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt, asrt, psrt, .int, rsrt, msrt],
          asserts := [wf, wfa, below, t.codes, t.sites, t.cond, o.hit, .eq (.var 7) o.finish.pending, .eq (.var 8) d.nextId,
            .eq (.var 9) d.records, .eq (.var 10) tbl] ++ goal,
          shows := List.range 11 }, o.hit)

def answerMLayout : Layout := answerMLayoutOf 3

def answerMScript (goal : List Term) : Except String (Script × Term) := answerMScriptOf 3 goal

def answerMCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: an answer's events reach machines: {m}"; return false
  let L := answerMLayout
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dm, nm) := L.find? startM.table | fail "no instance table"
  let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no instance slot"
  let some (de, _) := L.find? (instEntry .int) | fail "no instance entry"
  let some (dtop, _) := L.find? (Ty.option (.tuple [.int, .int])) | fail "no timer option"
  let some (dp, np) := L.find? (pendingTable writeShapes) | fail "no pending table"
  let some (dpt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry writeShapes]) | fail "no pending slot"
  let some (dpe, _) := L.find? (pendingEntry writeShapes) | fail "no pending entry"
  let some (d1, _) := L.find? (.tuple [.int]) | fail "no key tuple"
  let some (dres, _) := L.find? (answerTy Ty.nil Ty.nil) | fail "no answer type"
  let Sr := slotsOf dr drt nr 2 (.var 0)
  let Sm := slotsOf dm dmt nm 2 (.var 5)
  let Sp := slotsOf dp dpt np 2 (.var 4)
  let entry := Sp[0]!.2[1]
  let goal := [Sr[0]!.1, .eq (Sr[0]!.2[0]) (.int 3), .not Sr[1]!.1, .not Sr[2]!.1,
    Sm[0]!.1, .eq (Sm[0]!.2[0]) (.int 3), .eq (Term.sel de 0 0 (Sm[0]!.2[1])) (.int 0),
    .is dtop 1 (Term.sel de 0 1 (Sm[0]!.2[1])), .not Sm[1]!.1, .not Sm[2]!.1,
    .eq (Term.sel d1 0 0 (Term.sel dpe 0 3 entry)) (.int 3), .not Sp[1]!.1, .not Sp[2]!.1,
    .eq (.var 1) (.int 100), .eq (.var 3) (.int 40), .is dres 0 (.var 6)]
  match answerMScript goal with
  | .error m => fail m
  | .ok (script, _) =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let after : SymState writeSvc := { records := .var 9, now := .var 1, fresh := .var 2, nextId := .var 8,
                                         pending := .var 7, machines := .cons (.var 10) .nil }
      match (SymState.vars 0).decode M L (v := writeSvc) prelude writeShapes,
          after.decode M L (v := writeSvc) prelude writeShapes,
          (vs.lookup 6).bind (decodeV L (answerTy Ty.nil Ty.nil)) with
      | some s, some s', some y =>
        let r := step prelude writeSvc s (.answer 2 ⟨answerTy Ty.nil Ty.nil, Ty.down _ rfl y⟩)
        let view (sms : List (Step.MachineState writeSvc.records writeSvc.event)) :=
          sms.map fun ⟨_, is⟩ => is.map fun i => (intDen _ i.key, intDen _ i.state, i.timer.map fun (d, st) => (d, intDen _ st))
        let sorted (ps : List (Step.Pending writeSvc.event)) := (ps.map pendView).mergeSort fun a b => a.1 ≤ b.1
        let mut ok := true
        if r.outcome.summary != "accepted" then ok ← fail s!"the step says {r.outcome.summary}"
        if !sameAs L recordsT rfl r.state.records (vs.lookup 9) then ok ← fail "the records differ from the step's"
        if view s'.machines.toSigma != view r.state.machines.toSigma || view s'.machines.toSigma != [[(some 3, some 1, some (105, some 2))]] then
          ok ← fail s!"the new table holds {view s'.machines.toSigma}, the step {view r.state.machines.toSigma}"
        if sorted s'.pending != sorted r.state.pending || s'.nextId != r.state.nextId ||
            (sorted s'.pending).map (·.1) != [40] then
          ok ← fail s!"the model's pending table holds {sorted s'.pending} and next id {s'.nextId}, the step {sorted r.state.pending} and {r.state.nextId}"
        if view s'.machines.toSigma == view s.machines.toSigma then ok ← fail "the table before the machine reacts passes the comparison"
        return ok
      | _, _, _ => fail "the model does not decode"
    | a => fail s!"{repr a}"

/-! An event whose reaction starts own commands beside a request, for `events_encode`: the service `w` above with the
reaction `mix`, which returns `[send_command(put, "alice", ev + 1, ..), request_command(send, ev + 2, ..),
send_command(put, "alice", ev + 3, ..)]`. From no records, no instances and next id 40, the event 3 starts key 3,
whose request takes id 40; the reaction's request takes 41, as own commands take no wire id, and the own commands
queue at places 0 and 1 in list order (inputs 4 and 6). The ids, the next id, and the own slots' places and inputs read
from the model must be what `applyEvents` leaves; the queue in the other order must not pass the comparison. The queue
read at place 1 (`queueAt`) must hold input 6, not the head's 4, and place 2 must hold nothing. -/

def putHandleE {Γ : List Ty} : Expr [] Γ (.dsl .command [recordsT, .int, .str, .int, .str]) :=
  .call (.prim .command [recordsT, .int, .str, .int, .str] rfl)
    (.cons (.str "put") (.cons (.list (.cons (.str "alice") .nil))
      (.cons (.close ⟨"m", 20, 1, 0⟩ .nil rfl rfl acceptsE)
        (.cons (.close ⟨"m", 20, 2, 0⟩ .nil rfl rfl twiceDecideE)
          (.cons (.close ⟨"m", 20, 3, 0⟩ .nil rfl rfl (.lam (.list .nil) : E (.fn [cctxT, recordsT] Ty.rules))) .nil)))))

def mixPutE (k : Int) : Expr [] [Ty.reactionCtx recordsT, .int] (.dsl .effect [.int]) :=
  let ev : Expr [] [Ty.reactionCtx recordsT, .int] .int := .var (.there .here)
  let body : Expr [] [.int] (.fn [Ty.result Ty.nil .str] (.list .int)) := .lam (.list (.cons (.var (.there .here)) .nil))
  let clo : Expr [] [Ty.reactionCtx recordsT, .int] (.dsl .closure [.fn [Ty.result Ty.nil .str] (.list .int)]) :=
    .close ⟨"m", 21, 1, 0⟩ (.cons ev .nil) rfl rfl body
  .call (.prim .sendCommand [recordsT, .int, .str, .int, .str] rfl)
    (.cons putHandleE (.cons (.str "alice") (.cons (.bin .add ev (.int k)) (.cons clo .nil))))

def mixE : Expr [] [] (.fn [Ty.reactionCtx recordsT, .int] (.list (.dsl .effect [.int]))) :=
  .lam (.list (.cons (mixPutE 1) (.cons (fanSendE 2) (.cons (mixPutE 3) .nil))))

def mixSvc : ServiceV := { writeSvc with name := "x", reactions := [⟨"mix", .closed mixE⟩] }

def mixShapes : List (PendingShape mixSvc.event) := shapes mixSvc

def putKey : OwnKey := .command .int "put" .str .int .str ⟨⟨"m", 21, 1, 0⟩, [.int]⟩

def mixLayout (slots : Nat) : Layout :=
  let lits := Tazuna.Smt.Expr.lits acceptsE ++ Tazuna.Smt.Expr.lits twiceDecideE ++ Tazuna.Smt.Expr.lits mixE
  Layout.addTys (listSlots (fun _ => slots) lits) { effects := [sendKey ⟨"m", 3, 7, 0⟩, sendKey ⟨"m", 4, 1, 0⟩], owns := [putKey] }
    (reactTys ++ [.tuple [.int], .tuple [], .list .int, cctxT, Ty.result (.list .int) .str, pendingTable mixShapes] ++
      Tazuna.Smt.Expr.tys insertE ++ Tazuna.Smt.Expr.tys invariantsE ++ Tazuna.Smt.Expr.tys wrapIntE ++
      Tazuna.Smt.Expr.tys mixE ++ Tazuna.Smt.Expr.tys acceptsE ++ Tazuna.Smt.Expr.tys twiceDecideE)

/-- v0..v5 the state (v5 the instance table), v6 the event value, v7 the next id after, v8 the queue place after, then
per request slot its flag and id, and per own slot its flag, place and effect. -/
def mixScript (slots : Nat) (goal : List Term) : Except String (Script × Nat × Nat) := do
  let L := mixLayout slots
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (apply, ca) ← enc (mixSvc.apply.code L)
  let senv ← enc (StepEnv.of L mixShapes)
  let (o, c) ← enc (encodeEvents L prelude mixSvc mixShapes senv apply S.now [(tt, ⟨[.var 6], rfl⟩)] S.records
    S.machines S.nextId (.int 0))
  let some wf := S.wf L (v := mixSvc) mixShapes | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable mixShapes) | throw "no pending sort"
  let some msrt := L.srt? startM.table | throw "no table sort"
  let some esrt := L.srt? (.dsl .effect [.int]) | throw "no effect sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let base := 9
  let news := o.news.zipIdx.flatMap fun (sl, j) =>
    [.eq (.var (base + 2 * j)) sl.flag, .eq (.var (base + 2 * j + 1)) sl.id]
  let ob := base + 2 * o.news.length
  let owns := o.owns.zipIdx.flatMap fun (sl, j) =>
    [.eq (.var (ob + 3 * j)) sl.flag, .eq (.var (ob + 3 * j + 1)) sl.place, .eq (.var (ob + 3 * j + 2)) sl.effect]
  let vars := [rsrt, .int, .int, .int, psrt, msrt, .int, .int, .int] ++
    (o.news.map fun _ => [Srt.bool, .int]).flatten ++ (o.owns.map fun _ => [Srt.bool, .int, esrt]).flatten
  let hb := vars.length
  let heads := [1, 2].zipIdx.flatMap fun (k, j) =>
    let (has, eff) := queueAt (.var (hb + 4)) o.owns (.int k)
    [.eq (.var (hb + 2 * j)) has, .eq (.var (hb + 2 * j + 1)) eff]
  let vars := vars ++ [.bool, esrt, .bool, esrt, esrt]
  pure ({ datatypes := dts, vars, asserts := [wf, ca, c, .eq (.var 7) o.nextId, .eq (.var 8) o.queued] ++ news ++ owns ++
            heads ++ goal,
          shows := List.range vars.length }, o.news.length, o.owns.length)

def mixCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: events queue own commands: {m}"; return false
  let L := mixLayout 3
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dm, nm) := L.find? startM.table | fail "no instance table"
  let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no instance slot"
  let some (dp, np) := L.find? (pendingTable mixShapes) | fail "no pending table"
  let some (dpt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry mixShapes]) | fail "no pending slot"
  let Sr := slotsOf dr drt nr 2 (.var 0)
  let Sm := slotsOf dm dmt nm 2 (.var 5)
  let Sp := slotsOf dp dpt np 2 (.var 4)
  let goal := (Sr ++ Sm ++ Sp).map (fun sl => Term.not sl.1) ++
    [.eq (.var 1) (.int 100), .eq (.var 3) (.int 40), .eq (.var 6) (.int 3)]
  match mixScript 3 goal with
  | .error m => fail m
  | .ok (script, nn, no) =>
    match ← solver.run script with
    | .sat vs =>
      match (SymState.vars 0).decode (modelOf vs) L (v := mixSvc) prelude mixShapes with
      | none => fail "the model does not decode"
      | some s =>
        match Step.applyEvents prelude ({ state := s } : Step.Acc mixSvc) [(3 : Int)] with
        | .error _ => fail "the step faults"
        | .ok a =>
          let flag (n : Nat) := vs.lookup n == some (.bool true)
          let ids := ((List.range nn).filterMap fun j =>
            if flag (9 + 2 * j) then natOf ((vs.lookup (10 + 2 * j)).getD (.int (-1))) else none).mergeSort (· ≤ ·)
          let ob := 9 + 2 * nn
          let inputOf : Val → Option Int
            | .ctor _ _ [_, .int x, _] => some x
            | _ => none
          let queue := (((List.range no).filterMap fun j =>
            if flag (ob + 3 * j) then
              match vs.lookup (ob + 3 * j + 1), (vs.lookup (ob + 3 * j + 2)).bind inputOf with
              | some (.int q), some x => some (q, x)
              | _, _ => none
            else none).mergeSort fun a b => a.1 ≤ b.1)
          let stepIds := ((a.state.pending.map (·.id)).mergeSort (· ≤ ·))
          let stepQueue : List Int := a.own.filterMap fun
            | .command _ _ i _ _ value _ => match Ty.same i .int with
              | some ⟨h⟩ => some (cast (congrArg Ty.den0 h) value)
              | none => none
            | _ => none
          let mut ok := true
          if ids != stepIds || ids != [40, 41] then ok ← fail s!"the wire ids are {ids}, the step's {stepIds}"
          if vs.lookup 7 != some (.int a.state.nextId) then ok ← fail s!"the next id is {repr (vs.lookup 7)}"
          if queue.map (·.1) != [0, 1] || vs.lookup 8 != some (.int 2) then
            ok ← fail s!"the queue places are {queue.map (·.1)}, the place after {repr (vs.lookup 8)}"
          if queue.map (·.2) != stepQueue || stepQueue != [4, 6] then
            ok ← fail s!"the queue holds {queue.map (·.2)}, the step's {stepQueue}"
          if queue.reverse.map (·.2) == stepQueue then ok ← fail "the queue in the other order passes the comparison"
          let hb := ob + 3 * no
          let atOne := (vs.lookup (hb + 1)).bind inputOf
          if vs.lookup hb != some (.bool true) || atOne != stepQueue[1]? then
            ok ← fail s!"the queue's place 1 holds {repr atOne}, the step's {stepQueue[1]?}"
          if atOne == stepQueue[0]? then ok ← fail "the queue's head passes as place 1"
          if vs.lookup (hb + 2) != some (.bool false) then ok ← fail "the queue has a place 2"
          return ok
    | a => fail s!"{repr a}"

/-! An own command's internal step, for `ownCommand_encode`: the command `twice` above runs as an own effect whose
`on_answer` captured 5 and returns [5] on any answer. From the state of `a command's events reach machines` (no
records, no instances, request 2 pending, next id 40, now 100), alice's `twice 3` applies 3 twice (key 3 starts with a
request at 40, then enters 1 with a request at 41), its `ensures` holds, and `on_answer` applies 5. The records,
instance table, next id and new wire ids read from the model must be what `Step.runCommand` leaves; applying only
`decide`'s events must not pass the comparison. -/

def answerFiveE : Expr [] [.int] (.fn [Ty.result Ty.nil .str] (.list .int)) := .lam (.list (.cons (.var (.there .here)) .nil))

def answerFive : Site [.int] (.fn [Ty.result Ty.nil .str] (.list .int)) := ⟨⟨"m", 22, 1, 0⟩, [], .nil, rfl, rfl, answerFiveE⟩

def internalLayoutOf (slots : Nat) : Layout := svcLayout twiceSvc slots (siteParts answerFive)

def internalLayout : Layout := internalLayoutOf 3

/-- v0..v5 the state (v4 the pending table, v5 the instance table), v6 the caller, v7 the input, v8 the records
after, v9 the next id after, v10 the instance table after, then per new request slot its flag and id. -/
def internalScriptOf (slots : Nat) (goal : List Term) : Except String (Script × Nat) := do
  let L := internalLayoutOf slots
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (cc, cx) ← enc (CommandCode.of L twiceC)
  let (apply, ca) ← enc (twiceSvc.apply.code L)
  let some ks := callerTerms L rfl twiceC.callers | throw "no caller terms"
  let senv ← enc (StepEnv.of L twiceShapes)
  let some five := Code.ofTerm? .int (.int 5) | throw "no capture code"
  let (o, cond) ← enc (encodeOwnCommand L prelude twiceSvc twiceShapes senv twiceC cc answerFive (five, ()) apply
    ks S.records S.now S.fresh S.nextId (.int 0) (.var 6) (.var 7) S.machines)
  let below ← enc (pendingBelowT L twiceShapes S.pending S.nextId)
  let some wf := S.wf L (v := twiceSvc) twiceShapes | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable twiceShapes) | throw "no pending sort"
  let some msrt := L.srt? startM.table | throw "no table sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [tbl] := o.answered.tables.toList | throw "not one machine"
  let news := o.decided.after.news ++ o.answered.news
  let slots := news.zipIdx.flatMap fun (sl, j) => [.eq (.var (11 + 2 * j)) sl.flag, .eq (.var (12 + 2 * j)) sl.id]
  pure ({ datatypes := dts,
          vars := [rsrt, .int, .int, .int, psrt, msrt, .str, .int, rsrt, .int, msrt] ++
            (news.map fun _ => [Srt.bool, .int]).flatten,
          asserts := [wf, below, cx, ca, cond, .eq (.var 8) o.answered.records, .eq (.var 9) o.answered.nextId,
            .eq (.var 10) tbl] ++ slots ++ goal,
          shows := List.range (11 + 2 * news.length) }, news.length)

def internalCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: an own command's internal step: {m}"; return false
  let L := internalLayout
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dm, nm) := L.find? startM.table | fail "no instance table"
  let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no instance slot"
  let some (dp, np) := L.find? (pendingTable twiceShapes) | fail "no pending table"
  let some (dpt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry twiceShapes]) | fail "no pending slot"
  let Sr := slotsOf dr drt nr 2 (.var 0)
  let Sm := slotsOf dm dmt nm 2 (.var 5)
  let Sp := slotsOf dp dpt np 2 (.var 4)
  let goal := [.not Sr[0]!.1, .not Sr[1]!.1, .not Sr[2]!.1, .not Sm[0]!.1, .not Sm[1]!.1, .not Sm[2]!.1,
    Sp[0]!.1, .eq (Sp[0]!.2[0]) (.int 2), .not Sp[1]!.1, .not Sp[2]!.1, .eq (.var 1) (.int 100),
    .eq (.var 3) (.int 40), .eq (.var 6) (.str "alice"), .eq (.var 7) (.int 3)]
  match internalScriptOf 3 goal with
  | .error m => fail m
  | .ok (script, nn) =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let after : SymState twiceSvc := { records := .var 8, now := .var 1, fresh := .var 2, nextId := .var 9,
                                         pending := .var 4, machines := .cons (.var 10) .nil }
      match (SymState.vars 0).decode M L (v := twiceSvc) prelude twiceShapes,
          after.decode M L (v := twiceSvc) prelude twiceShapes with
      | some s, some s' =>
        let view (sms : List (Step.MachineState twiceSvc.records twiceSvc.event)) :=
          sms.map fun ⟨m, is⟩ => is.map fun (i : Step.Instance m) =>
            (intDen _ i.key, intDen _ i.state, i.timer.map fun (p : Int × m.state.den0) => (p.1, intDen _ p.2))
        let flag (n : Nat) := vs.lookup n == some (.bool true)
        let ids := ((List.range nn).filterMap fun j =>
          if flag (11 + 2 * j) then natOf ((vs.lookup (12 + 2 * j)).getD (.int (-1))) else none).mergeSort (· ≤ ·)
        match Step.runCommand prelude ({ state := s } : Step.Acc twiceSvc) twiceC ("alice" : String) (3 : Int)
            (answerFive.fn ((5 : Int), ())) with
        | .error _ => fail "the internal step faults"
        | .ok a =>
          let stepIds := ((a.state.pending.filter (·.id != 2)).map (·.id)).mergeSort (· ≤ ·)
          let mut ok := true
          if !sameAs L recordsT rfl a.state.records (vs.lookup 8) then ok ← fail "the records differ from the step's"
          if view s'.machines.toSigma != view a.state.machines.toSigma then
            ok ← fail s!"the new table holds {view s'.machines.toSigma}, the step {view a.state.machines.toSigma}"
          if ids != stepIds || vs.lookup 9 != some (.int a.state.nextId) || ids.take 2 != [40, 41] then
            ok ← fail s!"the new wire ids are {ids} and next id {repr (vs.lookup 9)}, the step's {stepIds} and {a.state.nextId}"
          if a.state.fresh != s.fresh + 1 then ok ← fail "the fresh counter did not advance"
          match Step.applyEvents prelude ({ state := s } : Step.Acc twiceSvc) [(3 : Int), (3 : Int)] with
          | .ok b =>
            if sameAs L recordsT rfl b.state.records (vs.lookup 8) && view s'.machines.toSigma == view b.state.machines.toSigma then
              ok ← fail "applying only decide's events passes the comparison"
          | .error _ => ok ← fail "decide's events fault"
          return ok
      | _, _ => fail "the model does not decode"
    | a => fail s!"{repr a}"

/-! An own query's internal step, for `ownQuery_encode`: the query `next` answers its input plus one, and its
`on_answer` returns the answer as the one event. From the same state, alice's `next 3` answers 4 and applies 4, so
key 4 starts with a request at 40. The records, instance table, next id and new wire ids read from the model must be
what `Step.runQuery` leaves; an `on_answer` that returns no event must not pass the comparison. -/

def nextResolveE : E (.fn [qctxT] .int) :=
  .lam (.bin .add (.field (ft := .int) "input" 1 (by simp) (.var .here)) (.int 1))

def nextQ : QueryV recordsT .str :=
  { name := "next", input := .int, output := .int, callers := ["alice"], accepts := .closed acceptsE,
    resolve := .closed nextResolveE }

def answerIsEventE : Expr [] [] (.fn [.int] (.list .int)) := .lam (.list (.cons (.var .here) .nil))

def answerIsEvent : Site [] (.fn [.int] (.list .int)) := ⟨⟨"m", 23, 1, 0⟩, [], .nil, rfl, rfl, answerIsEventE⟩

def answerNone : Site [] (.fn [.int] (.list .int)) := ⟨⟨"m", 23, 2, 0⟩, [], .nil, rfl, rfl, .lam (.list .nil)⟩

def ownQueryLayout : Layout :=
  Layout.addTys (fun _ => 3) twiceLayout (Tazuna.Smt.Expr.tys nextResolveE)

/-- v0..v5 the state, v6 the caller, v7 the input, v8 the records after, v9 the next id after, v10 the instance table
after, then per new request slot its flag and id. -/
def ownQueryScript (goal : List Term) : Except String (Script × Nat) := do
  let L := ownQueryLayout
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (qc, cq) ← enc (QueryCode.of L nextQ)
  let (apply, ca) ← enc (twiceSvc.apply.code L)
  let some ks := callerTerms L rfl nextQ.callers | throw "no caller terms"
  let senv ← enc (StepEnv.of L twiceShapes)
  let (o, cond) ← enc (encodeOwnQuery L prelude twiceSvc twiceShapes senv nextQ qc answerIsEvent () apply ks
    S.records S.now S.nextId (.int 0) (.var 6) (.var 7) S.machines)
  let below ← enc (pendingBelowT L twiceShapes S.pending S.nextId)
  let some wf := S.wf L (v := twiceSvc) twiceShapes | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable twiceShapes) | throw "no pending sort"
  let some msrt := L.srt? startM.table | throw "no table sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [tbl] := o.answered.tables.toList | throw "not one machine"
  let news := o.answered.news
  let slots := news.zipIdx.flatMap fun (sl, j) => [.eq (.var (11 + 2 * j)) sl.flag, .eq (.var (12 + 2 * j)) sl.id]
  pure ({ datatypes := dts,
          vars := [rsrt, .int, .int, .int, psrt, msrt, .str, .int, rsrt, .int, msrt] ++
            (news.map fun _ => [Srt.bool, .int]).flatten,
          asserts := [wf, below, cq, ca, cond, .eq (.var 8) o.answered.records, .eq (.var 9) o.answered.nextId,
            .eq (.var 10) tbl] ++ slots ++ goal,
          shows := List.range (11 + 2 * news.length) }, news.length)

def ownQueryCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: an own query's internal step: {m}"; return false
  let L := ownQueryLayout
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dm, nm) := L.find? startM.table | fail "no instance table"
  let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no instance slot"
  let some (dp, np) := L.find? (pendingTable twiceShapes) | fail "no pending table"
  let some (dpt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry twiceShapes]) | fail "no pending slot"
  let Sr := slotsOf dr drt nr 2 (.var 0)
  let Sm := slotsOf dm dmt nm 2 (.var 5)
  let Sp := slotsOf dp dpt np 2 (.var 4)
  let goal := [.not Sr[0]!.1, .not Sr[1]!.1, .not Sr[2]!.1, .not Sm[0]!.1, .not Sm[1]!.1, .not Sm[2]!.1,
    Sp[0]!.1, .eq (Sp[0]!.2[0]) (.int 2), .not Sp[1]!.1, .not Sp[2]!.1, .eq (.var 1) (.int 100),
    .eq (.var 3) (.int 40), .eq (.var 6) (.str "alice"), .eq (.var 7) (.int 3)]
  match ownQueryScript goal with
  | .error m => fail m
  | .ok (script, nn) =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let after : SymState twiceSvc := { records := .var 8, now := .var 1, fresh := .var 2, nextId := .var 9,
                                         pending := .var 4, machines := .cons (.var 10) .nil }
      match (SymState.vars 0).decode M L (v := twiceSvc) prelude twiceShapes,
          after.decode M L (v := twiceSvc) prelude twiceShapes with
      | some s, some s' =>
        let view (sms : List (Step.MachineState twiceSvc.records twiceSvc.event)) :=
          sms.map fun ⟨m, is⟩ => is.map fun (i : Step.Instance m) =>
            (intDen _ i.key, intDen _ i.state, i.timer.map fun (p : Int × m.state.den0) => (p.1, intDen _ p.2))
        let flag (n : Nat) := vs.lookup n == some (.bool true)
        let ids := ((List.range nn).filterMap fun j =>
          if flag (11 + 2 * j) then natOf ((vs.lookup (12 + 2 * j)).getD (.int (-1))) else none).mergeSort (· ≤ ·)
        let run (site : Site [] (.fn [.int] (.list .int))) :=
          Step.runQuery prelude ({ state := s } : Step.Acc twiceSvc) nextQ ("alice" : String) (3 : Int) (site.fn ())
        match run answerIsEvent, run answerNone with
        | .ok a, .ok b =>
          let stepIds := ((a.state.pending.filter (·.id != 2)).map (·.id)).mergeSort (· ≤ ·)
          let mut ok := true
          if !sameAs L recordsT rfl a.state.records (vs.lookup 8) then ok ← fail "the records differ from the step's"
          if view s'.machines.toSigma != view a.state.machines.toSigma then
            ok ← fail s!"the new table holds {view s'.machines.toSigma}, the step {view a.state.machines.toSigma}"
          if ids != stepIds || vs.lookup 9 != some (.int a.state.nextId) || ids != [40] then
            ok ← fail s!"the new wire ids are {ids} and next id {repr (vs.lookup 9)}, the step's {stepIds} and {a.state.nextId}"
          if sameAs L recordsT rfl b.state.records (vs.lookup 8) && view s'.machines.toSigma == view b.state.machines.toSigma then
            ok ← fail "an on_answer without events passes the comparison"
          return ok
        | _, _ => fail "the internal step faults"
      | _, _ => fail "the model does not decode"
    | a => fail s!"{repr a}"

/-! An own effect's internal step, for `ownStep_encode`: the service lists the command `twice` and the query `next` above,
and the layout has three own kinds, `twice`, `next` and `gone`, which the service does not list, and a fourth,
`twice` answered at a site the program lacks, which no effect has and which must not stop the encoding. From the same state,
the effect term is in turn alice's `twice 3` with 5 captured, her `next 3`, and her `gone 3`. The records, instance
table, next id, fresh counter and new wire ids read from the model must be what `Step.runOwn` leaves for the effect,
and must differ from what it leaves for the other kind's effect; `gone` must fault as `Step.runOwn` does. -/

def dispSvc : ServiceV := { twiceSvc with name := "o", queries := [nextQ] }

def dispShapes : List (PendingShape dispSvc.event) := shapes dispSvc

def dispSites : List AnySite := writeSites ++ [⟨[.int], _, answerFive⟩, ⟨[], _, answerIsEvent⟩]

def twiceKey : OwnKey := .command .int "twice" .str .int .str ⟨answerFive.site, [.int]⟩
def nextKey : OwnKey := .query .int "next" .str .int .int ⟨answerIsEvent.site, []⟩
def goneKey : OwnKey := .command .int "gone" .str .int .str ⟨answerFive.site, [.int]⟩
def deadKey : OwnKey := .command .int "twice" .str .int .str ⟨⟨"m", 77, 77, 0⟩, [.int]⟩

/-- The service `o`'s layout, in a program that writes the `on_answer` sites the effects name, with the own kinds
`twice`, `next` and `gone` added by hand: the effects are terms of the case, not of a function the service keeps, so
the builder makes none of them. `dead` adds own kinds no handle makes. -/
def dispLayoutOf (slots : Nat) (dead : List OwnKey := []) : Layout :=
  let L := svcLayout dispSvc slots (joinParts [siteParts answerFive, siteParts answerIsEvent,
    ⟨[], [], [Ty.nil, Ty.result Ty.nil .str, .tuple [.int], .tuple []], []⟩])
  Layout.addTys (fun _ => slots) { L with owns := L.owns ++ [twiceKey, nextKey, goneKey] ++ dead } []

/-- v0..v5 the state, v6 the effect, v7 the records after, v8 the next id after, v9 the instance table after, v10 the
fault, v11 the fresh counter after, then per new request slot its flag and id. -/
def dispScriptOf (slots : Nat) (effect : Layout → Except Refusal Term) (goal : List Term) (dead : List OwnKey := []) :
    Except String (Script × Nat × OwnStepOut dispSvc) := do
  let L := dispLayoutOf slots dead
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (apply, ca) ← enc (dispSvc.apply.code L)
  let senv ← enc (StepEnv.of L dispShapes)
  let eff ← enc (effect L)
  let ⟨o, cond, codes⟩ ← enc (encodeOwnStep L prelude dispSites dispSvc dispShapes senv apply S.records S.now
    S.fresh S.nextId (.int 0) (.var 6) S.machines)
  let below ← enc (pendingBelowT L dispShapes S.pending S.nextId)
  let some wf := S.wf L (v := dispSvc) dispShapes | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable dispShapes) | throw "no pending sort"
  let some msrt := L.srt? startM.table | throw "no table sort"
  let some esrt := L.srt? (.dsl .effect [.int]) | throw "no effect sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [tbl] := o.terms.done.tables.toList | throw "not one machine"
  let news := o.terms.done.news
  let slots := news.zipIdx.flatMap fun (sl, j) => [.eq (.var (12 + 2 * j)) sl.flag, .eq (.var (13 + 2 * j)) sl.id]
  pure ({ datatypes := dts,
          vars := [rsrt, .int, .int, .int, psrt, msrt, esrt, rsrt, .int, msrt, .bool, .int] ++
            (news.map fun _ => [Srt.bool, .int]).flatten,
          asserts := [wf, below, ca, codes, cond, .eq (.var 6) eff, .eq (.var 7) o.terms.done.records,
            .eq (.var 8) o.terms.done.nextId, .eq (.var 9) tbl, .eq (.var 10) o.terms.fault,
            .eq (.var 11) o.terms.fresh] ++ slots ++ goal,
          shows := List.range (12 + 2 * news.length) }, news.length, o)

def dispCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: an own effect's internal step: {m}"; return false
  let L := dispLayoutOf 3 [deadKey]
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dm, nm) := L.find? startM.table | fail "no instance table"
  let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no instance slot"
  let some (dp, np) := L.find? (pendingTable dispShapes) | fail "no pending table"
  let some (dpt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry dispShapes]) | fail "no pending slot"
  let Sr := slotsOf dr drt nr 2 (.var 0)
  let Sm := slotsOf dm dmt nm 2 (.var 5)
  let Sp := slotsOf dp dpt np 2 (.var 4)
  let goal := [.not Sr[0]!.1, .not Sr[1]!.1, .not Sr[2]!.1, .not Sm[0]!.1, .not Sm[1]!.1, .not Sm[2]!.1,
    Sp[0]!.1, .eq (Sp[0]!.2[0]) (.int 2), .not Sp[1]!.1, .not Sp[2]!.1, .eq (.var 1) (.int 100),
    .eq (.var 2) (.int 7), .eq (.var 3) (.int 40)]
  let twiceFx : EffectV dispSvc.event := .command "twice" .str .int .str ("alice" : String) (3 : Int) (answerFive.fn ((5 : Int), ()))
  let nextFx : EffectV dispSvc.event := .query "next" .str .int .int ("alice" : String) (3 : Int) (answerIsEvent.fn ())
  let goneFx : EffectV dispSvc.event := .command "gone" .str .int .str ("alice" : String) (3 : Int) (answerFive.fn ((5 : Int), ()))
  let cases : List (String × (Layout → Except Refusal Term) × EffectV dispSvc.event × EffectV dispSvc.event) :=
    [("twice", fun L => ownT L twiceKey (.str "alice") (.int 3) [.int 5], twiceFx, nextFx),
     ("next", fun L => ownT L nextKey (.str "alice") (.int 3) [], nextFx, twiceFx),
     ("gone", fun L => ownT L goneKey (.str "alice") (.int 3) [.int 5], goneFx, twiceFx)]
  let mut ok := true
  for (name, effect, fx, other) in cases do
    match dispScriptOf 3 effect goal [deadKey] with
    | .error m => ok ← fail s!"{name}: {m}"
    | .ok (script, nn, o) =>
      match ← solver.run script with
      | .sat vs =>
        let M := modelOf vs
        let after : SymState dispSvc := { records := .var 7, now := .var 1, fresh := .var 11, nextId := .var 8,
                                          pending := .var 4, machines := .cons (.var 9) .nil }
        match (SymState.vars 0).decode M L (v := dispSvc) prelude dispShapes,
            after.decode M L (v := dispSvc) prelude dispShapes with
        | some s, some s' =>
          let view (sms : List (Step.MachineState dispSvc.records dispSvc.event)) :=
            sms.map fun ⟨m, is⟩ => is.map fun (i : Step.Instance m) =>
              (intDen _ i.key, intDen _ i.state, i.timer.map fun (p : Int × m.state.den0) => (p.1, intDen _ p.2))
          let flag (n : Nat) := vs.lookup n == some (.bool true)
          let ids := ((List.range nn).filterMap fun j =>
            if flag (12 + 2 * j) then natOf ((vs.lookup (13 + 2 * j)).getD (.int (-1))) else none).mergeSort (· ≤ ·)
          let same (a : Step.Acc dispSvc) : Bool :=
            sameAs L recordsT rfl a.state.records (vs.lookup 7) && view s'.machines.toSigma == view a.state.machines.toSigma &&
              vs.lookup 8 == some (.int a.state.nextId) && vs.lookup 11 == some (.int a.state.fresh) &&
              ids == ((a.state.pending.filter (·.id != 2)).map (·.id)).mergeSort (· ≤ ·)
          let faults := flag 10
          match Step.runOwn prelude ({ state := s } : Step.Acc dispSvc) fx,
              Step.runOwn prelude ({ state := s } : Step.Acc dispSvc) other with
          | .ok a, .ok b =>
            if faults || (o.fault? M).isSome then ok ← fail s!"{name}: the model faults, the step does not"
            if !same a then
              ok ← fail s!"{name}: the model's records, table, next id {repr (vs.lookup 8)}, fresh {repr (vs.lookup 11)} or wire ids {ids} differ from the step's (next id {a.state.nextId}, fresh {a.state.fresh})"
            if same b then ok ← fail s!"{name}: the other kind's internal step passes the comparison"
          | .error f, _ =>
            let got := (o.fault? M).map fun g => (Outcome.fault g).summary
            if !faults || got != some (Outcome.fault f).summary then
              ok ← fail s!"{name}: the step faults with {(Outcome.fault f).summary}, the model with {got}"
          | _, .error _ => ok ← fail s!"{name}: the other kind's internal step faults"
        | _, _ => ok ← fail s!"{name}: the model does not decode"
      | a => ok ← fail s!"{name}: {repr a}"
  return ok

/-! The cascade, for `settle_encode`: the own queue holds alice's `twice 3` (5 captured) and her `next 3`, at places 0
and 1, in the state of the case above. With two internal steps both run, and the records, instance table, next id,
fresh counter and new wire ids read from the model must be what `Step.settleFrom` leaves, and must differ from what
the first internal step alone leaves. With one internal step the occupied place 1 is past the bound: the model must
name `Fault.cascadeLimit`. A queue whose head is `gone 3` faults there, and the step after it does not run. -/

/-- Names each term the cascade's fault reads by a fresh variable, so the fault is read from the solver's values instead
of evaluating the terms in Lean, which unfolds their shared subterms into trees. -/
abbrev Named := StateM (Nat × List Srt × List Term)

def named (srt : Srt) (t : Term) : Named Term := modifyGet fun (n, vs, eqs) =>
  (.var n, (n + 1, vs ++ [srt], eqs ++ [.eq (.var n) t]))

def namedRules (rs : List (Term × Term)) : Named (List (Term × Term)) :=
  rs.mapM fun (n, b) => do pure (← named .str n, ← named .bool b)

def namedKind {v : ServiceV} : OwnKindOut v → Named (OwnKindOut v)
  | .command name o => do
    pure (.command name { o with callerOk := ← named .bool o.callerOk, rules := ← namedRules o.rules,
                                 decided := { o.decided with ok := ← named .bool o.decided.ok,
                                                             ensures := ← namedRules o.decided.ensures } })
  | .query name o => do
    pure (.query name { o with callerOk := ← named .bool o.callerOk, rules := ← namedRules o.rules })
  | .missing name => pure (.missing name)

def namedSettle {v : ServiceV} (o : SettleOut v) : Named (SettleOut v) := do
  let steps ← o.steps.mapM fun (act, so) => do
    let kinds ← so.kinds.mapM fun (t, k) => do pure (← named .bool t, ← namedKind k)
    pure (← named .bool act, { so with kinds, terms := { so.terms with fault := ← named .bool so.terms.fault } })
  pure { o with steps, over := ← named .bool o.over }

/-- v0..v5 the state, v6 the records after, v7 the next id after, v8 the instance table after, v9 whether an internal
step faults, v10 whether a place past the bound is occupied, v11 the fresh counter after, then per new request slot
its flag and id. -/
def cascadeTermsOf (slots fuel : Nat) (effects : List (Layout → Except Refusal Term)) (goal : List Term) :
    Except String (Script × Nat × SettleOut dispSvc) := do
  let L := dispLayoutOf slots
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (apply, ca) ← enc (dispSvc.apply.code L)
  let senv ← enc (StepEnv.of L dispShapes)
  let effs ← effects.mapM fun f => enc (f L)
  let queue : List OwnSlot := effs.zipIdx.map fun (e, j) => ⟨tt, .int j, e⟩
  let t : StepTerms dispSvc := ⟨.bool false, ⟨S.records, S.machines, S.nextId, [], [], .int effs.length⟩, S.fresh⟩
  let ⟨o, cond, codes⟩ ← enc (encodeSettle L prelude dispSites dispSvc dispShapes senv apply (effs.headD tt) S.now
    fuel 0 queue t)
  let below ← enc (pendingBelowT L dispShapes S.pending S.nextId)
  let some wf := S.wf L (v := dispSvc) dispShapes | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable dispShapes) | throw "no pending sort"
  let some msrt := L.srt? startM.table | throw "no table sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [tbl] := o.terms.done.tables.toList | throw "not one machine"
  let news := o.terms.done.news
  let slots := news.zipIdx.flatMap fun (sl, j) => [.eq (.var (12 + 2 * j)) sl.flag, .eq (.var (13 + 2 * j)) sl.id]
  pure ({ datatypes := dts,
          vars := [rsrt, .int, .int, .int, psrt, msrt, rsrt, .int, msrt, .bool, .bool, .int] ++
            (news.map fun _ => [Srt.bool, .int]).flatten,
          asserts := [wf, below, ca, codes, cond, .eq (.var 6) o.terms.done.records, .eq (.var 7) o.terms.done.nextId,
            .eq (.var 8) tbl, .eq (.var 9) o.terms.fault, .eq (.var 10) o.over, .eq (.var 11) o.terms.fresh] ++ slots ++
            goal,
          shows := List.range (12 + 2 * news.length) }, news.length, o)

def cascadeScriptOf (slots fuel : Nat) (effects : List (Layout → Except Refusal Term)) (goal : List Term) :
    Except String (Script × Nat × SettleOut dispSvc) := do
  let (script, nn, o) ← cascadeTermsOf slots fuel effects goal
  let (o', (_, vs, eqs)) := (namedSettle o).run (script.vars.length, [], [])
  pure ({ script with vars := script.vars ++ vs, asserts := script.asserts ++ eqs,
                      shows := List.range (script.vars.length + vs.length) }, nn, o')

def cascadeCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: the cascade: {m}"; return false
  let L := dispLayoutOf 3
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dm, nm) := L.find? startM.table | fail "no instance table"
  let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no instance slot"
  let some (dp, np) := L.find? (pendingTable dispShapes) | fail "no pending table"
  let some (dpt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry dispShapes]) | fail "no pending slot"
  let Sr := slotsOf dr drt nr 2 (.var 0)
  let Sm := slotsOf dm dmt nm 2 (.var 5)
  let Sp := slotsOf dp dpt np 2 (.var 4)
  let goal := [.not Sr[0]!.1, .not Sr[1]!.1, .not Sr[2]!.1, .not Sm[0]!.1, .not Sm[1]!.1, .not Sm[2]!.1,
    Sp[0]!.1, .eq (Sp[0]!.2[0]) (.int 2), .not Sp[1]!.1, .not Sp[2]!.1, .eq (.var 1) (.int 100),
    .eq (.var 2) (.int 7), .eq (.var 3) (.int 40)]
  let twiceT : Layout → Except Refusal Term := fun L => ownT L twiceKey (.str "alice") (.int 3) [.int 5]
  let nextT : Layout → Except Refusal Term := fun L => ownT L nextKey (.str "alice") (.int 3) []
  let goneT : Layout → Except Refusal Term := fun L => ownT L goneKey (.str "alice") (.int 3) [.int 5]
  let twiceFx : EffectV dispSvc.event := .command "twice" .str .int .str ("alice" : String) (3 : Int) (answerFive.fn ((5 : Int), ()))
  let nextFx : EffectV dispSvc.event := .query "next" .str .int .int ("alice" : String) (3 : Int) (answerIsEvent.fn ())
  let goneFx : EffectV dispSvc.event := .command "gone" .str .int .str ("alice" : String) (3 : Int) (answerFive.fn ((5 : Int), ()))
  let cases : List (String × Nat × List (Layout → Except Refusal Term) × List (EffectV dispSvc.event)) :=
    [("two internal steps", 2, [twiceT, nextT], [twiceFx, nextFx]),
     ("one internal step", 1, [twiceT, nextT], [twiceFx, nextFx]),
     ("a faulting head", 2, [goneT, twiceT], [goneFx, twiceFx])]
  let mut ok := true
  for (name, fuel, effects, fxs) in cases do
    match cascadeScriptOf 3 fuel effects goal with
    | .error m => ok ← fail s!"{name}: {m}"
    | .ok (script, nn, o) =>
      match ← solver.run script with
      | .sat vs =>
        let M := modelOf vs
        let after : SymState dispSvc := { records := .var 6, now := .var 1, fresh := .var 11, nextId := .var 7,
                                          pending := .var 4, machines := .cons (.var 8) .nil }
        match (SymState.vars 0).decode M L (v := dispSvc) prelude dispShapes,
            after.decode M L (v := dispSvc) prelude dispShapes with
        | some s, some s' =>
          let view (sms : List (Step.MachineState dispSvc.records dispSvc.event)) :=
            sms.map fun ⟨m, is⟩ => is.map fun (i : Step.Instance m) =>
              (intDen _ i.key, intDen _ i.state, i.timer.map fun (p : Int × m.state.den0) => (p.1, intDen _ p.2))
          let flag (n : Nat) := vs.lookup n == some (.bool true)
          let ids := ((List.range nn).filterMap fun j =>
            if flag (12 + 2 * j) then natOf ((vs.lookup (13 + 2 * j)).getD (.int (-1))) else none).mergeSort (· ≤ ·)
          let same (a : Step.Acc dispSvc) : Bool :=
            sameAs L recordsT rfl a.state.records (vs.lookup 6) && view s'.machines.toSigma == view a.state.machines.toSigma &&
              vs.lookup 7 == some (.int a.state.nextId) && vs.lookup 11 == some (.int a.state.fresh) &&
              ids == ((a.state.pending.filter (·.id != 2)).map (·.id)).mergeSort (· ≤ ·)
          let a0 : Step.Acc dispSvc := { state := s, own := fxs }
          let got := (o.fault? M).map fun g => (Outcome.fault g).summary
          match Step.settleFrom prelude fuel 0 a0, Step.runOwn prelude a0 (fxs.headD nextFx) with
          | .ok a, first =>
            if (o.fault? M).isSome then ok ← fail s!"{name}: the model faults with {got}, the cascade does not"
            if !same a then
              ok ← fail s!"{name}: the model's records, table, next id {repr (vs.lookup 7)}, fresh {repr (vs.lookup 11)} or wire ids {ids} differ from the cascade's (next id {a.state.nextId}, fresh {a.state.fresh})"
            match first with
            | .ok b => if same b then ok ← fail s!"{name}: the first internal step alone passes the comparison"
            | .error _ => ok ← fail s!"{name}: the first internal step faults"
          | .error f, _ =>
            if got != some (Outcome.fault f).summary then
              ok ← fail s!"{name}: the cascade faults with {(Outcome.fault f).summary}, the model with {got}"
        | _, _ => ok ← fail s!"{name}: the model does not decode"
      | a => ok ← fail s!"{name}: {repr a}"
  return ok

/-! A whole event step with its cascade, for `step_encode`: the service `c` is `w` above with the command `put` (`twice`
renamed) and the reaction `once`, which queues alice's `put (ev + 10)`, answered with no events, for an event below 5.
From no records, no instances, request 2 pending, next id 40, fresh 7 and now 100, the event 3 runs through the events
loop and queues `put 13`. With bound 1 the internal step runs and the step is accepted: the records, table, pending
ids, next id and fresh counter read from the model must be the step's, and must differ from what the events alone leave.
With bound 0 the queued `put` is past the bound, and the model must name `Fault.cascadeLimit` as the step does. -/

def onceBodyE : Expr [] [] (.fn [Ty.result Ty.nil .str] (.list .int)) := .lam (.list .nil)

def onceSite : Site [] (.fn [Ty.result Ty.nil .str] (.list .int)) := ⟨⟨"m", 24, 1, 0⟩, [], .nil, rfl, rfl, onceBodyE⟩

def oncePutE : Expr [] [Ty.reactionCtx recordsT, .int] (.dsl .effect [.int]) :=
  let ev : Expr [] [Ty.reactionCtx recordsT, .int] .int := .var (.there .here)
  let clo : Expr [] [Ty.reactionCtx recordsT, .int] (.dsl .closure [.fn [Ty.result Ty.nil .str] (.list .int)]) :=
    .close ⟨"m", 24, 1, 0⟩ .nil rfl rfl onceBodyE
  .call (.prim .sendCommand [recordsT, .int, .str, .int, .str] rfl)
    (.cons putHandleE (.cons (.str "alice") (.cons (.bin .add ev (.int 10)) (.cons clo .nil))))

def onceE : Expr [] [] (.fn [Ty.reactionCtx recordsT, .int] (.list (.dsl .effect [.int]))) :=
  .lam (boolCase (.bin .lt (.var (.there .here)) (.int 5)) (.list (.cons oncePutE .nil)) (.list .nil))

def cascSvc (cascade : Int) : ServiceV :=
  { writeSvc with name := "c", commands := [{ twiceC with name := "put" }], reactions := [⟨"once", .closed onceE⟩],
                  bounds := ⟨[], 0, cascade, 0⟩ }

def cascShapes (cascade : Int) : List (PendingShape (cascSvc cascade).event) := shapes (cascSvc cascade)

def cascSites : List AnySite := writeSites ++ [⟨[], _, onceSite⟩]

def onceKey : OwnKey := .command .int "put" .str .int .str ⟨⟨"m", 24, 1, 0⟩, []⟩

def cascLayout (cascade : Int) (slots : Nat) : Layout := svcLayout (cascSvc cascade) slots

/-- The builder's own kinds are the handles a function of the step makes, each with the `on_answer` sites that
function writes: `once` sends `put` with its site, so `put` at that site is the only kind, even with `twice` listed
too and other sites of the same type in the program. -/
def unsentSvc : ServiceV := { cascSvc 1 with commands := [{ twiceC with name := "put" }, twiceC] }

def ownKindsCheck : IO Bool := do
  let owns := (svcLayout unsentSvc 2 (siteParts answerFive)).owns
  if owns.length == 1 && owns.all (·.same onceKey) then return true
  IO.println s!"smt-check: own kinds: {owns.length} kinds, not put at once's site alone"
  return false

/-- v0..v5 the state, v6 the event value, v7 the records after, v8 the fresh counter after, v9 the next id after, v10
the pending table after, v11 the instance table after. -/
def cascEventTermsOf (cascade : Int) (slots : Nat) (goal : List Term) :
    Except String (Script × FinishOut (cascSvc cascade)) := do
  let v := cascSvc cascade
  let shs := cascShapes cascade
  let L := cascLayout cascade slots
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (o, t) ← eventTerms L cascSites v ⟨0, by simp [v, cascSvc, writeSvc, writeSvcOf]⟩ S (.var 6)
  let fo := o.finish
  let below ← enc (pendingBelowT L shs S.pending S.nextId)
  let some wf := S.wf L (v := v) shs | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable shs) | throw "no pending sort"
  let some msrt := L.srt? startM.table | throw "no table sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let d := fo.settle.terms.done
  let [tbl] := d.tables.toList | throw "not one machine"
  let script : Script :=
    { datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, msrt, .int, rsrt, .int, .int, psrt, msrt],
      asserts := [wf, below, t.codes, t.cond, t.sites, .eq (.var 7) d.records, .eq (.var 8) fo.settle.terms.fresh,
        .eq (.var 9) d.nextId, .eq (.var 10) fo.pending, .eq (.var 11) tbl] ++ goal }
  pure (script, fo)

/-- `cascEventTermsOf` with the cascade's and the invariants' terms named after its variables. -/
def cascEventScriptOf (cascade : Int) (slots : Nat) (goal : List Term) :
    Except String (Script × FinishOut (cascSvc cascade) × List (Term × Term)) := do
  let (script, fo) ← cascEventTermsOf cascade slots goal
  let ((so, invs), (_, vs, eqs)) := (do pure (← namedSettle fo.settle, ← namedRules fo.invariants)).run
    (script.vars.length, [], [])
  pure ({ script with vars := script.vars ++ vs, asserts := script.asserts ++ eqs,
                      shows := List.range (script.vars.length + vs.length) }, { fo with settle := so }, invs)

def cascEventCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: an event's cascade: {m}"; return false
  let mut ok := true
  for (name, cascade) in [("bound 1", (1 : Int)), ("bound 0", 0)] do
    let v := cascSvc cascade
    let shs := cascShapes cascade
    let L := cascLayout cascade 5
    let some (dr, nr) := L.find? recordsT | return ← fail "no records"
    let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | return ← fail "no records slot"
    let some (dm, nm) := L.find? startM.table | return ← fail "no instance table"
    let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | return ← fail "no instance slot"
    let some (dp, np) := L.find? (pendingTable shs) | return ← fail "no pending table"
    let some (dpt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry shs]) | return ← fail "no pending slot"
    let Sr := slotsOf dr drt nr 2 (.var 0)
    let Sm := slotsOf dm dmt nm 2 (.var 5)
    let Sp := slotsOf dp dpt np 2 (.var 4)
    let goal := (Sr ++ Sm ++ Sp.drop 1).map (fun sl => Term.not sl.1) ++
      [Sp[0]!.1, .eq (Sp[0]!.2[0]) (.int 2), .eq (.var 1) (.int 100), .eq (.var 2) (.int 7),
        .eq (.var 3) (.int 40), .eq (.var 6) (.int 3)]
    match cascEventScriptOf cascade 5 goal with
    | .error m => ok ← fail s!"{name}: {m}"
    | .ok (script, fo, invs) =>
      match ← solver.run script with
      | .sat vs =>
        let M := modelOf vs
        let after : SymState v := { records := .var 7, now := .var 1, fresh := .var 8, nextId := .var 9,
                                    pending := .var 10, machines := .cons (.var 11) .nil }
        match (SymState.vars 0).decode M L (v := v) prelude shs, after.decode M L (v := v) prelude shs with
        | some s, some s' =>
          let view (sms : List (Step.MachineState v.records v.event)) :=
            sms.map fun ⟨m, is⟩ => is.map fun (i : Step.Instance m) =>
              (intDen _ i.key, intDen _ i.state, i.timer.map fun (p : Int × m.state.den0) => (p.1, intDen _ p.2))
          let ids (st : State v) := (st.pending.map (·.id)).mergeSort (· ≤ ·)
          let same (st : State v) : Bool :=
            sameAs L recordsT rfl st.records (vs.lookup 7) && view s'.machines.toSigma == view st.machines.toSigma &&
              s'.nextId == st.nextId && s'.fresh == st.fresh && ids s' == ids st
          let r := step prelude v s (.event ⟨0, by simp [v, cascSvc, writeSvc, writeSvcOf]⟩ (3 : Int))
          let got := (fo.settle.fault? M).map fun g => (Outcome.fault g).summary
          match fo.settle.fault? M, brokenIn M invs, r.outcome with
          | none, [], .accepted =>
            if !same r.state then
              ok ← fail s!"{name}: the model's state (next id {s'.nextId}, fresh {s'.fresh}, ids {ids s'}) is not the step's (next id {r.state.nextId}, fresh {r.state.fresh}, ids {ids r.state})"
            match Step.applyEvents prelude ({ state := s } : Step.Acc v) [(3 : Int)] with
            | .ok a => if same a.state then ok ← fail s!"{name}: the events without the cascade pass the comparison"
            | .error _ => ok ← fail s!"{name}: the events fault"
          | some _, _, .fault f =>
            if got != some (Outcome.fault f).summary then
              ok ← fail s!"{name}: the step faults with {(Outcome.fault f).summary}, the model with {got}"
          | _, _, out => ok ← fail s!"{name}: the step says {out.summary}, the model {got}"
        | _, _ => ok ← fail s!"{name}: the model does not decode"
      | a => ok ← fail s!"{name}: {repr a}"
  return ok

/-! A clock line whose timers queue own commands, for `step_encode`: the machine `tick` is `start` whose effect, for a key
below 10, is alice's `put (key + 10)` answered with no events, in the service `c` above without its reaction. Its
program makes no request, so nothing is pending. From the state of `clock fires timers` without its record and its
request (keys 7 and 3 due at 80 and 90, next id 40, now 50), the line at 100
fires key 7 then key 3, each round queueing its `put` at the round's queue place; with bound 2 both internal steps run
and the step is accepted. The records, table, pending ids, next id and fresh counter read from the model must be the
step's, and must differ from what the rounds alone leave. -/

def tickEffectE : Expr [] [] (.fn [invCtxT] (Ty.option (.dsl .effect [.int]))) :=
  let ctx : Expr [] [invCtxT] invCtxT := .var .here
  let key : Expr [] [invCtxT] .int := .field (ft := .int) "key" 0 (by simp) ctx
  let clo : Expr [] [invCtxT] (.dsl .closure [.fn [Ty.result Ty.nil .str] (.list .int)]) :=
    .close ⟨"m", 24, 1, 0⟩ .nil rfl rfl onceBodyE
  let put : Expr [] [invCtxT] (.dsl .effect [.int]) :=
    .call (.prim .sendCommand [recordsT, .int, .str, .int, .str] rfl)
      (.cons putHandleE (.cons (.str "alice") (.cons (.bin .add key (.int 10)) (.cons clo .nil))))
  .lam (boolCase (.bin .lt key (.int 10)) (.ctor (vs := [[Ty.dsl .effect [.int]], []]) ⟨0, by decide⟩ (.cons put .nil))
    (.ctor (vs := [[Ty.dsl .effect [.int]], []]) ⟨1, by decide⟩ .nil))

def tickM : MachineV recordsT .int := { startM with name := "tick", effect := .closed tickEffectE }

def tickSvc (cascade : Int) : ServiceV := { cascSvc cascade with name := "tk", machines := [tickM], reactions := [] }

/-- The service `tk`'s sites: those of its functions, as its program has. -/
def tickSites (cascade : Int) : List AnySite := (svcParts (tickSvc cascade)).sites

def tickShapes (cascade : Int) : List (PendingShape (tickSvc cascade).event) := shapes (tickSvc cascade)

def tickLayout (cascade : Int) (slots : Nat) : Layout := svcLayout (tickSvc cascade) slots

/-- v0..v5 the state, v6 the line's time, v7 the records after, v8 the fresh counter after, v9 the next id after, v10
the pending table after, v11 the instance table after, v12 whether every round fired. -/
def tickClockTermsOf (cascade : Int) (slots : Nat) (goal : List Term) :
    Except String (Script × ClockOut (tickSvc cascade)) := do
  let v := tickSvc cascade
  let shs := tickShapes cascade
  let L := tickLayout cascade slots
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let t ← stepOf L (tickSites cascade) v S (fun _ => pure (.clock (.var 6)))
  let .clock o := t.out | throw "not a clock line's terms"
  let below ← enc (pendingBelowT L shs S.pending S.nextId)
  let some wf := S.wf L (v := v) shs | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable shs) | throw "no pending sort"
  let some msrt := L.srt? tickM.table | throw "no table sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let d := o.finish.settle.terms.done
  let [tbl] := d.tables.toList | throw "not one machine"
  pure ({ datatypes := dts,
          vars := [rsrt, .int, .int, .int, psrt, msrt, .int, rsrt, .int, .int, psrt, msrt, .bool],
          asserts := [wf, below, t.codes, t.sites, t.cond, .eq (.var 7) d.records, .eq (.var 8) o.finish.settle.terms.fresh,
            .eq (.var 9) d.nextId, .eq (.var 10) o.finish.pending, .eq (.var 11) tbl, .eq (.var 12) o.over] ++ goal,
          shows := List.range 13 }, o)

def tickClockCheck (solver : Solver) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: timers queue own commands: {m}"; return false
  let v := tickSvc 2
  let shs := tickShapes 2
  let L := tickLayout 2 5
  let some (dr, nr) := L.find? recordsT | fail "no records"
  let some (drt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | fail "no records slot"
  let some (dm, nm) := L.find? tickM.table | fail "no instance table"
  let some (dmt, _) := L.find? (.tuple [Ty.bool, .int, instEntry .int]) | fail "no instance slot"
  let some (de, _) := L.find? (instEntry .int) | fail "no instance entry"
  let some (dto, _) := L.find? (Ty.option (.tuple [.int, .int])) | fail "no timer option"
  let some (dp, _) := L.find? (.tuple [.int, .int]) | fail "no timer"
  let some (d, n) := L.find? (pendingTable shs) | fail "no pending table"
  let some (dt, _) := L.find? (.tuple [Ty.bool, .dsl .fresh [], pendingEntry shs]) | fail "no pending slot"
  let Sr := slotsOf dr drt nr 2 (.var 0)
  let Sm := slotsOf dm dmt nm 2 (.var 5)
  let Sp := slotsOf d dt n 2 (.var 4)
  let waits (j : Nat) (key dl : Int) := [Sm[j]!.1, .eq (Sm[j]!.2[0]) (.int key),
    .eq (Term.sel de 0 0 (Sm[j]!.2[1])) (.int 0), .is dto 0 (Term.sel de 0 1 (Sm[j]!.2[1])),
    .eq (.sel dp 0 0 (.sel dto 0 0 (Term.sel de 0 1 (Sm[j]!.2[1])))) (.int dl),
    .eq (.sel dp 0 1 (.sel dto 0 0 (Term.sel de 0 1 (Sm[j]!.2[1])))) (.int 1)]
  let goal := [.eq (.var 1) (.int 50), .eq (.var 6) (.int 100), .eq (.var 3) (.int 40), .eq (.var 2) (.int 7)] ++
    ((Sr ++ Sm.drop 2 ++ Sp).map fun sl => Term.not sl.1) ++ waits 0 7 80 ++ waits 1 3 90
  match tickClockTermsOf 2 5 goal with
  | .error m => fail m
  | .ok (script, _) =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let after : SymState v := { records := .var 7, now := .var 6, fresh := .var 8, nextId := .var 9,
                                  pending := .var 10, machines := .cons (.var 11) .nil }
      match (SymState.vars 0).decode M L (v := v) prelude shs, after.decode M L (v := v) prelude shs with
      | some s, some s' =>
        let view (sms : List (Step.MachineState v.records v.event)) :=
          sms.map fun ⟨m, is⟩ => is.map fun (i : Step.Instance m) =>
            (intDen _ i.key, intDen _ i.state, i.timer.map fun (p : Int × m.state.den0) => (p.1, intDen _ p.2))
        let ids (st : State v) := (st.pending.map (·.id)).mergeSort (· ≤ ·)
        let same (st : State v) : Bool :=
          sameAs L recordsT rfl st.records (vs.lookup 7) && view s'.machines.toSigma == view st.machines.toSigma &&
            s'.nextId == st.nextId && s'.fresh == st.fresh && ids s' == ids st
        let r := step prelude v s (.clock 100)
        let mut ok := true
        if vs.lookup 12 == some (.bool true) then ok ← fail "the script says every round fired"
        if r.outcome.summary != "accepted" then ok ← fail s!"the step says {r.outcome.summary}"
        if r.state.fresh != s.fresh + 2 then ok ← fail s!"the step ran {r.state.fresh - s.fresh} internal steps, not 2"
        if !same r.state then
          ok ← fail s!"the model's state (next id {s'.nextId}, fresh {s'.fresh}, ids {ids s'}, table {view s'.machines.toSigma}) is not the step's (next id {r.state.nextId}, fresh {r.state.fresh}, ids {ids r.state}, table {view r.state.machines.toSigma})"
        match Step.fire { s with now := 100 } (v.bounds.cascadeNat + 1) with
        | some (s1, _) => if same s1 then ok ← fail "the rounds without the cascade pass the comparison"
        | none => ok ← fail "the rounds exceed the bound"
        return ok
      | _, _ => fail "the model does not decode"
    | a => fail s!"{repr a}"

/-- A chain of `depth` levels where each level builds the same shared term twice as two objects over the level
below: what an encoder does when it shares a term at each use instead of where it is built. Its script has one
definition per level, and printing it must not compare the copies as trees (exponential in depth). -/
def reshared (depth : Nat) : Script :=
  let level (t : Term) : Term := match (List.replicate 2 t).map (fun t => (Term.or t (.not t)).share) with
    | [a, b] => .and a b
    | _ => t
  { vars := [.bool], asserts := [(List.range depth).foldl (fun t _ => level t) (.var 0)] }

/-- Prints `reshared depth` within a second, with one definition per level. On a timeout the process exits at once:
the printing still runs and might not end. -/
def reshareCheck (depth : Nat) : IO Bool := do
  let task := Task.spawn (prio := .dedicated) fun _ => match (reshared depth).shared with
    | some (_, ds) => ds.length
    | none => 0
  let start ← IO.monoMsNow
  while !(← IO.hasFinished task) && (← IO.monoMsNow) - start < 1000 do IO.sleep 10
  unless ← IO.hasFinished task do
    IO.println "smt-check: re-shared chain: printing took over 1000 ms (shared copies compared as trees?)"
    IO.Process.exit 1
  if task.get != depth then
    IO.println s!"smt-check: re-shared chain: {task.get} definitions, want {depth}"; return false
  return true

/-! prove's questions (`questions`, `question_sound`): on the event service with the machine `calm`, each target's
question is sat, and the step from the state and input the model decodes to reaches its end in a state that breaks the
target's rule (`Step.settled`). On the cascade service `c`, whose reaction queues an own `put (ev + 10)` that accepts
only positive inputs, the cascade's targets: with bound 1 the own effect `put` can be Invalid, and with bound 0 the
queued `put` is past the bound; each question's decoded step faults as the target says (`Target.covers`). A question
asking the target's terms not to hold must not pass that comparison. -/

def settledBreaks (v : ServiceV) (s : State v) (x : Input v) : Target → Bool
  | .invariant none (some r) => match Step.settled prelude s x with
    | some a => (Step.broken (v.invariants.fn (a.state.records, ()))).contains r
    | none => false
  | .invariant (some m) (some r) => match Step.settled prelude s x with
    | some a => a.state.machines.toSigma.any fun ⟨m', insts⟩ => m'.name == m && insts.any fun i =>
        (Step.broken (m'.invariants.fn (.inl (i.key, i.state, a.state.records, a.state.now, ()), ()))).contains r
    | none => false
  | .invariant _ none => false
  | g => match (step prelude v s x).outcome with
    | .fault f => g.covers f
    | _ => false

def proveCase (solver : Solver) (name : String) (v : ServiceV) (hc : v.caller.isData = true) (P : List AnySite)
    (i : Fin v.subscribes.length) (want asked : List Target) : IO Bool := do
  let fail (m : String) : IO Bool := do IO.println s!"smt-check: prove's questions, {name}: {m}"; return false
  let L := svcLayout v 3
  let .ok senv := StepEnv.of L (shapes v) | fail "no step environment"
  let inp : SymInput v (shapes v) senv.nT := .event i (.var (5 + v.machines.length))
  match questions L prelude P v senv inp with
  | .error r => fail s!"no questions: {repr r}"
  | .ok (gs, qs) =>
    unless gs == want do return ← fail s!"the targets are {repr gs}"
    let mut ok := true
    for q in qs do
      let some g := q.target | continue
      unless asked.contains g do continue
      for negated in [false, true] do
        let asserts := if negated then q.script.asserts.dropLast ++ q.script.asserts.getLast?.toList.map .not
          else q.script.asserts
        match ← solver.run { q.script with asserts } with
        | .sat vs =>
          let M := modelOf vs
          match (SymState.vars (v := v) 0).decode M L prelude (shapes v), inp.decode M L hc with
          | some st, some x =>
            if settledBreaks v st x g == negated then
              ok ← fail s!"{repr g} (negated {negated}): the step from the model's state and input disagrees"
          | _, _ => ok ← fail s!"{repr g}: the model does not decode"
        | a => ok ← fail s!"{repr g} (negated {negated}): {repr a}"
    return ok

def proveCheck (solver : Solver) : IO Bool := do
  let a ← proveCase solver "machine invariants" evMSvc rfl [] evMI
    [.invariant none (some "small"), .invariant (some "calm") (some "calm")]
    [.invariant none (some "small"), .invariant (some "calm") (some "calm")]
  let b ← proveCase solver "cascade bound 1" (cascSvc 1) rfl cascSites ⟨0, by decide⟩
    [.invariant none (some "small"), .invariant (some "start") none, .effect "put", .cascade] [.effect "put", .cascade]
  let c ← proveCase solver "cascade bound 0" (cascSvc 0) rfl cascSites ⟨0, by decide⟩
    [.invariant none (some "small"), .invariant (some "start") none, .cascade] [.cascade]
  return a && b && c

def check (z3 : String) : IO Bool := do
  let solver : Solver := { path := z3, timeoutMs := 10000 }
  let mut ok := true
  for (slots, list) in [((fun _ => 3 : Ty → Nat), cases), ((fun _ => 3 : Ty → Nat), listCases), (reslots, reslotted)] do
    for (name, ⟨t, e⟩) in list do
      match scriptOf slots e with
      | .ok (L, script) =>
        match ← solver.run script with
        | .sat vs =>
          -- The value read back decodes (T3) to a value `==` to what eval computes.
          let same := match (vs.lookup 0).bind (decodeV L t) with
            | some y => Ty.deq t y (Expr.eval (G := []) .nil () e ())
            | none => false
          if !same then
            IO.println s!"smt-check: {name}: the solver's value differs from eval's"; ok := false
        | a => IO.println s!"smt-check: {name}: {repr a}"; ok := false
      | .error m => IO.println s!"smt-check: {name}: {m}"; ok := false
  for (slots, list) in [((fun _ => 1 : Ty → Nat), overflows), (reslots, reslotOverflows)] do
    for (name, ⟨_, e⟩) in list do
      match scriptOf slots e with
      | .ok (_, script) =>
        match ← solver.run script with
        | .unsat => pure ()
        | a => IO.println s!"smt-check: {name}: not unsat: {repr a}"; ok := false
      | .error m => IO.println s!"smt-check: {name}: {m}"; ok := false
  for (step, index) in [(0, 0), (5, -3), (2, 7), (40, -1)] do
    match freshScript step index with
    | .ok (L, script) =>
      match ← solver.run script with
      | .sat vs =>
        let back := ((vs.lookup 0).bind (decodeV L .id)).bind (embedV L .id)
        if back.map (·.print) != (embedV L .id ((freshOf index).eval (G := []) .nil () (step, ()))).map (·.print) then
          IO.println s!"smt-check: fresh({step}, {index}): the solver's id differs from eval's"; ok := false
      | a => IO.println s!"smt-check: fresh({step}, {index}): {repr a}"; ok := false
    | .error m => IO.println s!"smt-check: fresh({step}, {index}): {m}"; ok := false
  for (name, goal) in illFormed do
    for (withWf, want) in [(true, "unsat"), (false, "sat")] do
      match illFormedScript withWf goal with
      | .ok script =>
        let got := match ← solver.run script with
          | .unsat => "unsat"
          | .sat _ => "sat"
          | _ => "unknown"
        if got != want then IO.println s!"smt-check: {name} (well-formedness {withWf}): {got}"; ok := false
      | .error m => IO.println s!"smt-check: {name}: {m}"; ok := false
  for (name, goal) in queryCases do
    unless ← queryCase solver name goal do ok := false
  for (name, goal) in eventCases do
    unless ← eventCase solver name goal do ok := false
  for (name, goal, mf) in evMCases do
    unless ← evMCase solver name goal mf do ok := false
  for (name, goal) in clockCases do
    unless ← clockCase solver name goal do ok := false
  for (name, goal) in commandCases do
    unless ← commandCase solver name goal do ok := false
  unless ← pendingCheck solver do ok := false
  unless ← doorCheck solver do ok := false
  unless ← orderCheck solver do ok := false
  unless ← answerCheck solver do ok := false
  unless ← boundCheck solver do ok := false
  unless ← effectCheck solver do ok := false
  unless ← ownEffectCheck solver do ok := false
  unless ← effectListCheck solver do ok := false
  unless ← machineEffectCheck solver do ok := false
  unless ← timerCheck solver do ok := false
  unless ← noEffectsCheck solver do ok := false
  unless ← invariantCheck solver do ok := false
  unless ← reactCheck solver do ok := false
  unless ← stayCheck solver do ok := false
  unless ← fireCheck solver do ok := false
  unless ← startsCheck solver do ok := false
  unless ← writeCheck solver do ok := false
  unless ← quietCheck solver do ok := false
  unless ← fanCheck solver do ok := false
  unless ← ownKindsCheck do ok := false
  unless ← clockFireCheck solver do ok := false
  unless ← eventsCheck solver do ok := false
  unless ← twiceCheck solver do ok := false
  unless ← answerMCheck solver do ok := false
  unless ← reshareCheck 40 do ok := false
  unless ← mixCheck solver do ok := false
  unless ← internalCheck solver do ok := false
  unless ← ownQueryCheck solver do ok := false
  unless ← dispCheck solver do ok := false
  unless ← cascadeCheck solver do ok := false
  unless ← cascEventCheck solver do ok := false
  unless ← tickClockCheck solver do ok := false
  unless ← proveCheck solver do ok := false
  -- A datatype value with a negative field and an empty constructor.
  match ← solver.run dt with
  | .sat vs =>
    let want := [(0, Val.ctor 1 0 [.ctor 0 0 [.int (-3), .str "x"]]), (1, Val.ctor 0 1 [])]
    if vs.map (fun (n, v) => (n, v.print)) != want.map (fun (n, v) => (n, v.print)) then
      IO.println "smt-check: datatype values differ"; ok := false
  | a => IO.println s!"smt-check: datatypes: {repr a}"; ok := false
  match ← solver.run { asserts := [.bool false] } with
  | .unsat => pure ()
  | a => IO.println s!"smt-check: false is not unsat: {repr a}"; ok := false
  return ok

/-- A script's size as the solver reads it: the number of applications in its text, definitions of shared terms
and declarations included. -/
def nodes (s : Script) : Nat := ((s.text []).getD "").foldl (fun n c => if c == '(' then n + 1 else n) 0

/-- The step scripts whose sizes are measured, each as a function of the slots (or the bound, or the levels). -/
def sizeRows : List (String × (Nat → Except String Script)) :=
  let queue : List (Layout → Except Refusal Term) :=
    [fun L => ownT L twiceKey (.str "alice") (.int 3) [.int 5], fun L => ownT L nextKey (.str "alice") (.int 3) []]
  [("event", fun k => (·.1) <$> writeScript k []),
   ("event list", fun k => (·.1) <$> eventsScript k []),
   ("command", fun k => (·.1) <$> twiceScriptOf k []),
   ("answer", fun k => (·.1) <$> answerMScriptOf k []),
   ("clock", fun k => (·.1) <$> clockFireScript 2 k []),
   ("own command step", fun k => (·.1) <$> internalScriptOf k []),
   ("own effect step (3 kinds)", fun k => (·.1) <$> dispScriptOf k queue[0]! []),
   ("cascade of 2", fun k => (·.1) <$> cascadeTermsOf k 2 queue []),
   ("cascade at 3 slots (bound, not slots)", fun k => (·.1) <$> cascadeTermsOf 3 k queue []),
   ("event with a cascade of 1", fun k => (·.1) <$> cascEventTermsOf 1 k []),
   ("event with a cascade at 3 slots (bound, not slots)", fun k => (·.1) <$> cascEventTermsOf k 3 []),
   ("clock whose timers queue own commands (bound 2)", fun k => (·.1) <$> tickClockTermsOf 2 k []),
   ("re-shared chain (levels, not slots)", fun k => pure (reshared k))]

/-- Prints the step scripts' sizes at 2, 4, 8 and 16, one row each. With a budget file, whose rows have the same form,
a size above its budget, a row without a budget or a budget without a row fails: the size of what the solver reads is
part of what a change must explain. A row stops at its first size over budget, since a term that is no longer shared
can grow exponentially and the larger scripts would not finish. -/
def sizes (budget : Option System.FilePath) : IO UInt32 := do
  let budgets ← match budget with
    | none => pure []
    | some path => pure <| ((← IO.FS.lines path).toList.filter (· != "")).map fun l =>
      match l.splitOn ": " with
      | [name, ns] => (name, ns.splitOn "/" |>.map String.toNat?)
      | _ => (l, [])
  let mut ok := true
  for (name, f) in sizeRows do
    let bs := budgets.lookup name
    if budget.isSome && bs.isNone then IO.println s!"smt-check: {name} has no budget"; ok := false
    let mut cells := #[]
    for (k, i) in [2, 4, 8, 16].zipIdx do
      match f k, (bs.getD [])[i]?.join with
      | .error m, _ => cells := cells.push s!"({m})"; ok := false
      | .ok s, b =>
        let n := nodes s
        cells := cells.push (toString n)
        if let some b := b then
          if n > b then IO.println s!"smt-check: {name} at {k} has {n} nodes, over its budget of {b}"; ok := false; break
        else if bs.isSome then IO.println s!"smt-check: {name} at {k} has no budget"; ok := false
    IO.println s!"{name}: {"/".intercalate cells.toList}"
  for (name, _) in budgets do
    unless sizeRows.any (·.1 == name) do IO.println s!"smt-check: the budget of {name} measures no row"; ok := false
  return if ok then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--sizes"] => sizes none
  | ["--sizes", budget] => sizes (some budget)
  | [z3] => return if ← check z3 then 0 else 1
  | _ => IO.eprintln "usage: smt-check <z3 executable> | smt-check --sizes [budget file]"; return 3
