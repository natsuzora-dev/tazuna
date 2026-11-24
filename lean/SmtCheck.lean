import Tazuna.Smt.Bounds
import Tazuna.Smt.Order
import Tazuna.Smt.Solver

/-! Runs the solver on printed scripts and reads its answers back: the theorems cover printing and reading our own
text, and this check covers what only the solver can say, that it reads the text as SMT-LIB and prints values the
reader reads. Each case encodes a closed expression, asks the solver for a variable equal to it, and compares the
value, decoded, with `eval`. Usage: smt-check <z3 executable>. -/

open Tazuna.Ir Tazuna.Smt

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

/-! A query step on a small service, for `query_step`: the records are a table of Int to Int, the query `get` takes a
key from the caller "alice", accepts a positive key, and answers `table.get(ctx.records, key)`. Each case asks the
solver for a state and input whose outcome terms meet a goal, decodes them, runs `step` on what they decode to, and
compares its outcome with what the outcome terms denote in the model. Every code is the service's own: the encoding
of the source its structure value keeps (`QueryCode.of`, `EventCode.of`, `CommandCode.of`, `Fun.code`). -/

def recordsT : Ty := .table .int .int
def ctxT : Ty := Ty.ctx recordsT .int .str

def acceptsE : E (.fn [.int] Ty.rules) :=
  .lam (.list (.cons (.tuple (.cons (.str "positive") (.cons (.bin .gt (.var .here) (.int 0)) .nil))) .nil))

def resolveE : E (.fn [ctxT] (Ty.option .int)) :=
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
    (recordsT :: .id :: Tazuna.Smt.Expr.tys acceptsE ++ Tazuna.Smt.Expr.tys resolveE)

/-- The script for one goal on the outcome terms: v0..v3 the state, v4 the caller, v5 the key, v6..v9 the outcome
terms (caller listed, the rule's holds and name, the output). -/
def queryScript (goal : List Term) : Except String (Script × QueryOut) := do
  let L := queryLayout
  let (qc, cq) ← (QueryCode.of L getQ).mapError fun r => s!"no encoding: {repr r}"
  let some ks := callerTerms L rfl getQ.callers | throw "no caller terms"
  let S := SymState.vars 0
  let (o, cond) ← (encodeQuery L getQ qc ks S.records S.now S.fresh (.var 4) (.var 5)).mapError
    fun r => s!"no encoding: {repr r}"
  let some wf := S.wf L (v := querySvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some osrt := L.srt? (Ty.option .int) | throw "no output sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(name, holds)] := o.rules | throw "not one rule"
  pure ({ datatypes := dts, vars := [rsrt, .int, .int, .int, .str, .int, .bool, .bool, .str, osrt],
          asserts := [cq, cond, wf,
            .eq (.var 6) o.callerOk, .eq (.var 7) holds, .eq (.var 8) name, .eq (.var 9) o.output] ++ goal,
          shows := List.range 10 }, o)

/-- Goals that only a state that does not decode meets: two occupied slots with one key, a negative counter. The
well-formedness makes each unsat, and each is sat without it. -/
def illFormed : List (String × Term) :=
  match queryLayout.find? recordsT, queryLayout.find? (.tuple [Ty.bool, .int, .int]) with
  | some (d, n), some (dt, _) =>
    let S := slotsOf d dt n 2 (.var 0)
    [("well-formedness excludes a repeated key",
        .and (.and S[0]!.1 S[1]!.1) (.eq (S[0]!.2.headD tt) (S[1]!.2.headD tt))),
     ("well-formedness excludes a negative counter", .lt (.var 2) (.int 0))]
  | _, _ => []

def illFormedScript (withWf : Bool) (goal : Term) : Except String Script := do
  let L := queryLayout
  let some wf := (SymState.vars 0).wf L (v := querySvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some dts := L.datatypes? | throw "no datatypes"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int], asserts := (if withWf then [wf] else []) ++ [goal] }

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
      match (SymState.vars 0).decode M L (v := querySvc) rfl prelude [],
          (SymInput.query i (.var 4) (.var 5)).decode M L (v := querySvc) rfl (fun j => j.elim0) (fun | ⟨0, _⟩ => rfl)
            (fun j => j.elim0) with
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

/-! An event step on a service without machines or reactions, for `event_step`: the subscription's value is a key
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
    (recordsT :: evT :: Tazuna.Smt.Expr.tys applyE ++ Tazuna.Smt.Expr.tys invariantsE)

def eventI : Fin eventSvc.subscribes.length := ⟨0, by decide⟩

/-- v0..v3 the state, v4 the value, v5 the records after, v6 the event, v7 and v8 the invariant's holds and name. -/
def eventScript (goal : List Term) : Except String Script := do
  let L := eventLayout
  let (ec, ce) ← (EventCode.of L eventSvc eventI).mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (o, cond) ← (encodeEvent L ec S.records (.var 4)).mapError fun r => s!"no encoding: {repr r}"
  let some wf := S.wf L (v := eventSvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some esrt := L.srt? evT | throw "no event sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(name, holds)] := o.invariants | throw "not one invariant"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, esrt, rsrt, esrt, .bool, .str],
         asserts := [ce, cond, wf,
           .eq (.var 5) o.records, .eq (.var 6) o.event, .eq (.var 7) holds, .eq (.var 8) name] ++ goal,
         shows := List.range 9 }

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
      match (SymState.vars 0).decode M L (v := eventSvc) rfl prelude [],
          (SymInput.event eventI (.var 4)).decode M L (v := eventSvc) rfl (fun j => j.elim0) (fun j => j.elim0)
            (fun | ⟨0, _⟩ => rfl) with
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

/-- A clock line on the event service, for `clock_step`: v0..v3 the state, v4 the line's time, v5 whether time moves
forward, v6 and v7 the invariant's holds and name. -/
def clockScript (goal : List Term) : Except String Script := do
  let L := eventLayout
  let (inv, ci) ← (eventSvc.invariants.code L).mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (o, cond) ← (encodeClock L (v := eventSvc) inv S.records S.now (.var 4)).mapError
    fun r => s!"no encoding: {repr r}"
  let some wf := S.wf L (v := eventSvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(name, holds)] := o.invariants | throw "not one invariant"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, .int, .bool, .bool, .str],
         asserts := [ci, cond, wf,
           .eq (.var 5) o.forward, .eq (.var 6) holds, .eq (.var 7) name] ++ goal,
         shows := List.range 8 }

def clockCase (solver : Solver) (name : String) (goal : List Term) : IO Bool := do
  match clockScript goal with
  | .error m => IO.println s!"smt-check: {name}: {m}"; return false
  | .ok script =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let L := eventLayout
      match (SymState.vars 0).decode M L (v := eventSvc) rfl prelude [],
          (SymInput.clock (.var 4)).decode M L (v := eventSvc) rfl (fun j => j.elim0) (fun j => j.elim0)
            (fun | ⟨0, _⟩ => rfl) with
      | some s, some x@(.clock time) =>
        let r := step prelude eventSvc s x
        let ok := match (M.vars 5).toBool, brokenIn M [(.var 7, .var 6)], r.outcome with
          | false, _, .invalid ["time moves forward"] => r.state.now == s.now
          | true, n :: _, .fault (.invariant n') => n == n' && r.state.now == s.now
          | true, [], .accepted => r.state.now == time && sameAs L recordsT rfl r.state.records (vs.lookup 0)
          | _, _, _ => false
        unless ok do IO.println s!"smt-check: {name}: step says {r.outcome.summary}, the terms differ"
        return ok
      | _, _ => IO.println s!"smt-check: {name}: the model does not decode"; return false
    | a => IO.println s!"smt-check: {name}: {repr a}"; return false

def clockCases : List (String × List Term) :=
  [ ("clock moves time on", [.var 5, .var 6, .lt (.var 1) (.var 4)]),
    ("clock reports a broken invariant", [.var 5, .not (.var 6)]),
    ("clock refuses an earlier time", [.not (.var 5)]) ]

/-! A command step on the event service, for `command_step`: `put` takes a key from the caller "alice", accepts a
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
  Layout.addTys (listSlots (fun _ => 3) lits) {} (recordsT :: evT :: .id :: Tazuna.Smt.Expr.tys acceptsE ++
    Tazuna.Smt.Expr.tys decideE ++ Tazuna.Smt.Expr.tys ensuresE ++ Tazuna.Smt.Expr.tys applyE ++
    Tazuna.Smt.Expr.tys invariantsE)

/-- v0..v3 the state, v4 the caller, v5 the key, then the outcome terms: v6 caller listed, v7 and v8 the `accepts`
rule, v9 accepted by `decide`, v10 the rejection, v11 the events, v12 and v13 the `ensures` rule, v14 the records
after, v15 and v16 the invariant. -/
def commandScript (goal : List Term) : Except String Script := do
  let L := commandLayout
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let (cc, cx) ← enc (CommandCode.of L putC)
  let (apply, ca) ← enc (commandSvc.apply.code L)
  let (inv, ci) ← enc (commandSvc.invariants.code L)
  let some ks := callerTerms L rfl putC.callers | throw "no caller terms"
  let S := SymState.vars 0
  let (o, cond) ← (encodeCommand L putC cc apply inv ks S.records S.now S.fresh (.var 4)
    (.var 5)).mapError fun r => s!"no encoding: {repr r}"
  let some wf := S.wf L (v := commandSvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some lsrt := L.srt? (.list evT) | throw "no events sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(an, ah)] := o.rules | throw "not one rule"
  let [(en, eh)] := o.ensures | throw "not one ensures rule"
  let [(iname, ih)] := o.invariants | throw "not one invariant"
  pure { datatypes := dts,
         vars := [rsrt, .int, .int, .int, .str, .int, .bool, .bool, .str, .bool, .str, lsrt, .bool, .str, rsrt, .bool,
           .str],
         asserts := [cx, ca, ci, cond, wf, .eq (.var 6) o.callerOk, .eq (.var 7) ah, .eq (.var 8) an, .eq (.var 9) o.ok,
           .eq (.var 10) o.rejection, .eq (.var 11) o.events, .eq (.var 12) eh, .eq (.var 13) en,
           .eq (.var 14) o.records, .eq (.var 15) ih, .eq (.var 16) iname] ++ goal,
         shows := List.range 17 }

def commandCase (solver : Solver) (name : String) (goal : List Term) : IO Bool := do
  match commandScript goal with
  | .error m => IO.println s!"smt-check: {name}: {m}"; return false
  | .ok script =>
    match ← solver.run script with
    | .sat vs =>
      let M := modelOf vs
      let L := commandLayout
      let i : Fin commandSvc.commands.length := ⟨0, by decide⟩
      match (SymState.vars 0).decode M L (v := commandSvc) rfl prelude [],
          (SymInput.command i (.var 4) (.var 5)).decode M L (v := commandSvc) rfl (fun | ⟨0, _⟩ => rfl)
            (fun j => j.elim0) (fun | ⟨0, _⟩ => rfl) with
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
  [⟨[.int], _, ⟨⟨"m", 1, 1⟩, [], .nil, rfl, rfl, payAnswerE⟩⟩, ⟨[.int], _, ⟨⟨"m", 2, 1⟩, [], .nil, rfl, rfl, rateAnswerE⟩⟩,
   ⟨[], _, ⟨⟨"m", 3, 1⟩, [], .nil, rfl, rfl, rateEnsuresE⟩⟩]

def askR : ReactionV recordsT .int := ⟨"ask", fun _ _ _ => []⟩

def fxDeclared : List (String × DeclaredV) :=
  [("fx", .externalCommand "pay" .str .int .str), ("fx", .externalQuery "rate" .str .int (.closed rateEnsuresE))]

def insertSvc : ServiceV := { querySvc with apply := .closed insertE, invariants := .closed invariantsE }

def pendingSvc : ServiceV := { insertSvc with name := "p", queries := [], reactions := [askR], declared := fxDeclared }

def pendingShapes : List (PendingShape pendingSvc.event) := shapes pendingSvc pendingSites

def pendingLayout : Layout :=
  let lits := Tazuna.Smt.Expr.lits insertE ++ Tazuna.Smt.Expr.lits invariantsE ++ Tazuna.Smt.Expr.lits payAnswerE ++
    Tazuna.Smt.Expr.lits rateAnswerE ++ Tazuna.Smt.Expr.lits rateEnsuresE
  Layout.addTys (listSlots (fun _ => 3) lits) {} (recordsT :: pendingTable pendingShapes :: .list .int ::
    Tazuna.Smt.Expr.tys insertE ++ Tazuna.Smt.Expr.tys invariantsE ++ Tazuna.Smt.Expr.tys payAnswerE ++
    Tazuna.Smt.Expr.tys rateAnswerE ++ Tazuna.Smt.Expr.tys rateEnsuresE)

/-- The pending table's slots in v4, and the entry datatype. -/
def pendingSlots : Option (List Slot × Nat) :=
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
  let id (j : Nat) := (S[j]!.2.headD tt)
  let entry (j : Nat) := (S[j]!.2.getD 1 tt)
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
      match (SymState.vars 0).decode (modelOf vs) pendingLayout (v := pendingSvc) rfl prelude pendingShapes with
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
    after := .closed (.lam (.ctor (vs := [[Ty.timer .int], []]) ⟨1, by decide⟩ .nil)), effect := fun _ _ _ _ => none,
    invariants := .closed (.lam (.list .nil)) }

def doorSvc : ServiceV := { querySvc with name := "d", queries := [], machines := [doorM] }

def doorLayout : Layout := Layout.addTys (fun _ => 3) {} [recordsT, doorM.table]

def doorScript (withWf : Bool) (goal : List Term) : Except String Script := do
  let L := doorLayout
  let some wf := (SymState.vars 0 1).wf L (v := doorSvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some msrt := L.srt? doorM.table | throw "no instance table sort"
  let some dts := L.datatypes? | throw "no datatypes"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, .int, msrt], asserts := (if withWf then [wf] else []) ++ goal,
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
  let key (j : Nat) := S[j]!.2.headD tt
  let entry (j : Nat) := S[j]!.2.getD 1 tt
  let timer (j : Nat) := Term.sel de 0 1 (entry j)
  pure ([S[0]!.1, S[1]!.1, .not S[2]!.1, .eq (key 0) (.int 3), .eq (.sel de 0 0 (entry 0)) (.int 1),
      .is dopt 0 (timer 0), .eq (.sel dtm 0 0 (.sel dopt 0 0 (timer 0))) (.int 10),
      .eq (.sel dtm 0 1 (.sel dopt 0 0 (timer 0))) (.int 2),
      .eq (key 1) (.int 1), .eq (.sel de 0 0 (entry 1)) (.int 0), .is dopt 1 (timer 1)],
    [("well-formedness excludes an instance key twice", .and (.and S[0]!.1 S[1]!.1) (.eq (key 0) (key 1)))])

def intDen : (t : Ty) → t.den0 → Option Int
  | .int, x => some x
  | _, _ => none

def doorCheck (solver : Solver) : IO Bool := do
  let some (goal, illFormed) := doorGoals | IO.println "smt-check: instances: no layout"; return false
  let mut ok := true
  match doorScript true goal with
  | .error m => IO.println s!"smt-check: instances: {m}"; ok := false
  | .ok script =>
    match ← solver.run script with
    | .sat vs =>
      match (SymState.vars 0 1).decode (modelOf vs) doorLayout (v := doorSvc) rfl prelude [] with
      | some s =>
        -- Slot 0 holds key 3 and slot 1 key 1, yet the instances come in key order.
        let insts := s.machines.map fun ⟨_, is⟩ => is.map fun i =>
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
   ⟨"Id", .id, rfl, [(IdV.fresh 3, IdV.fresh 4), (IdV.fresh 9, IdV.named "a"), (IdV.named "a", IdV.fresh 1),
     (IdV.named "b", IdV.named "a")]⟩,
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

/-! An answer step on the pending service, for `answer_step` and `answer_unmatched`: the answer to the `rate` request
(shape 1) in slot 0. `rate` ensures a positive answer, its `on_answer` yields the answer plus the captured value, the
records insert that event, and the invariant `small` holds below three keys. -/

/-- v0..v4 the state, v5 the wire id, v6 the answer, then the outcome terms: v7 the slot holds the request, v8 and v9
the `ensures` rule, v10 the events, v11 the records after, v12 and v13 the invariant, v14 the pending table after.
`shift` adds to the answer the terms read, which breaks the encoding on purpose. -/
def answerScript (shift : Int) (goal : List Term) : Except String Script := do
  let L := pendingLayout
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let some sh := pendingShapes[1]? | throw "no rate shape"
  let (apply, ca) ← enc (pendingSvc.apply.code L)
  let (inv, ci) ← enc (pendingSvc.invariants.code L)
  let S := SymState.vars 0
  let (o, cond) ← enc (encodeAnswer L pendingShapes 1 sh 0 apply inv S.records S.pending (.var 5)
    (.add (.var 6) (.int shift)))
  let some wf := S.wf L (v := pendingSvc) pendingShapes | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable pendingShapes) | throw "no pending sort"
  let some lsrt := L.srt? (.list .int) | throw "no events sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(rn, rh)] := o.rules | throw "not one rule"
  let [(iname, ih)] := o.invariants | throw "not one invariant"
  pure { datatypes := dts,
         vars := [rsrt, .int, .int, .int, psrt, .int, .int, .bool, .bool, .str, lsrt, rsrt, .bool, .str, psrt],
         asserts := [ca, ci, cond, wf, .le (.int 0) (.var 5), .eq (.var 7) o.hit, .eq (.var 8) rh, .eq (.var 9) rn,
           .eq (.var 10) o.events, .eq (.var 11) o.records, .eq (.var 12) ih, .eq (.var 13) iname,
           .eq (.var 14) o.pending] ++ goal,
         shows := List.range 15 }

/-- The script whose goal is that no slot holds a request of the answer's type that the wire id names. -/
def unmatchedScript : Except String Script := do
  let L := pendingLayout
  let u ← (answerUnmatchedT L pendingShapes .int (.var 4) (.var 5)).mapError fun r => s!"no encoding: {repr r}"
  let some wf := (SymState.vars 0).wf L (v := pendingSvc) pendingShapes | throw "no well-formedness"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some psrt := L.srt? (pendingTable pendingShapes) | throw "no pending sort"
  let some dts := L.datatypes? | throw "no datatypes"
  -- Slot 0 holds a request with the wire id, so the answer names a request of another type.
  let some (S, _) := pendingSlots | throw "no layout"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, psrt, .int, .int],
         asserts := [wf, u, .le (.int 0) (.var 5), S[0]!.1, .eq (S[0]!.2.headD tt) (.var 5)], shows := List.range 7 }

/-- Runs the step from the decoded state and input and compares it with what the terms say; true when they agree. -/
def answerAgrees (vs : List (Nat × Val)) (unmatched : Bool) : Bool :=
  let M := modelOf vs
  let L := pendingLayout
  match (SymState.vars 0).decode M L (v := pendingSvc) rfl prelude pendingShapes, natOf (M.vars 5), intOf (M.vars 6) with
  | some s, some to, some value =>
    let r := step prelude pendingSvc s (.answer to ⟨.int, value⟩)
    if unmatched then r.outcome.summary == s!"fault answerUnmatched {to}" && r.state.pending.length == s.pending.length
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

/-! Bounds, for `createsT_iff` and `boundReached_iff`: records of two tables of Int to Int, `a` created at most 3
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
    Tazuna.Smt.Expr.tys tableA ++ [Ty.rules])

def boundI : Fin boundSvc.subscribes.length := ⟨0, by decide⟩

/-- v0..v3 the state, v4 the value, v5 the records after, v6 the bound-reached condition. `atMostB` is the `at_most`
the script encodes for `b`, and `withLimits` whether it asserts the limits of the state before. -/
def boundScript (atMostB : Int) (withLimits : Bool) (goal : List Term) : Except String Script := do
  let L := boundLayout
  let enc {α : Type} (x : Except Refusal α) : Except String α := x.mapError fun r => s!"no encoding: {repr r}"
  let (ec, ce) ← enc (EventCode.of L boundSvc boundI)
  let S := SymState.vars 0
  let (o, cond) ← enc (encodeEvent L ec S.records (.var 4))
  let (pre, cpre) ← enc (createsT L S.records (createsB atMostB))
  let (reached, creached) ← enc (boundReachedT L (createsB atMostB) cond o.records)
  let some wf := S.wf L (v := boundSvc) [] | throw "no well-formedness"
  let some rsrt := L.srt? recordsB | throw "no records sort"
  let some esrt := L.srt? evT | throw "no event sort"
  let some dts := L.datatypes? | throw "no datatypes"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, esrt, rsrt, .bool],
         asserts := [ce, cpre, creached, wf] ++ (if withLimits then [pre] else []) ++
           [.eq (.var 5) o.records, .eq (.var 6) reached] ++ goal,
         shows := List.range 7 }

/-- Whether the step from the decoded state and value leaves the bounds as the terms say it does. -/
def boundAgrees (vs : List (Nat × Val)) (reached : Bool) : Bool :=
  let M := modelOf vs
  let L := boundLayout
  match (SymState.vars 0).decode M L (v := boundSvc) rfl prelude [],
      (SymInput.event boundI (.var 4)).decode M L (v := boundSvc) rfl (fun j => j.elim0) (fun j => j.elim0)
        (fun | ⟨0, _⟩ => rfl) with
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
  let clo : Expr [] [.int] (.dsl .closure [answerTyE]) := .close ⟨"m", 3, 7⟩ (.cons (.var .here) .nil) rfl rfl body
  .call (.prim .requestCommand effArgs rfl) (.cons handle (.cons (.bin .add (.var .here) (.int k)) (.cons clo .nil)))

def sendKey (site : SiteId) : EffectKey :=
  ⟨.int, "send", .int, Ty.nil, some Ty.nil, none, ⟨site, [.int]⟩⟩

def effLayout : Layout :=
  Layout.addEffects (fun _ => 2) (Layout.addTys (fun _ => 2) { effects := [sendKey ⟨"m", 9, 9⟩, sendKey ⟨"m", 3, 7⟩] }
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

def main (args : List String) : IO UInt32 := do
  match args with
  | [z3] => return if ← check z3 then 0 else 1
  | _ => IO.eprintln "usage: smt-check <z3 executable>"; return 3
