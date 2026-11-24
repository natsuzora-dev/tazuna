import Tazuna.Smt.StepEncode
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
  let some wf := S.wf L (v := querySvc) | throw "no well-formedness"
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
  let some wf := (SymState.vars 0).wf L (v := querySvc) | throw "no well-formedness"
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
      match (SymState.vars 0).decode M L (v := querySvc) rfl [] [],
          (SymInput.query i (.var 4) (.var 5)).decode M L (v := querySvc) rfl (fun j => j.elim0) (fun | ⟨0, _⟩ => rfl)
            (fun j => j.elim0) with
      | some s, some x =>
        let r := step querySvc s x
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
  let some wf := S.wf L (v := eventSvc) | throw "no well-formedness"
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
      match (SymState.vars 0).decode M L (v := eventSvc) rfl [] [],
          (SymInput.event eventI (.var 4)).decode M L (v := eventSvc) rfl (fun j => j.elim0) (fun j => j.elim0)
            (fun | ⟨0, _⟩ => rfl) with
      | some s, some x =>
        let r := step eventSvc s x
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
  let some wf := S.wf L (v := eventSvc) | throw "no well-formedness"
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
      match (SymState.vars 0).decode M L (v := eventSvc) rfl [] [],
          (SymInput.clock (.var 4)).decode M L (v := eventSvc) rfl (fun j => j.elim0) (fun j => j.elim0)
            (fun | ⟨0, _⟩ => rfl) with
      | some s, some x@(.clock time) =>
        let r := step eventSvc s x
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
  let some wf := S.wf L (v := commandSvc) | throw "no well-formedness"
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
      match (SymState.vars 0).decode M L (v := commandSvc) rfl [] [],
          (SymInput.command i (.var 4) (.var 5)).decode M L (v := commandSvc) rfl (fun | ⟨0, _⟩ => rfl)
            (fun j => j.elim0) (fun | ⟨0, _⟩ => rfl) with
      | some s, some x =>
        let r := step commandSvc s x
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
