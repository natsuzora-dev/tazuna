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

/-- The script asking for a variable equal to the expression under its condition. -/
def scriptOf (slots : Ty → Nat) {t : Ty} (e : E t) : Except String (Layout × Script) := do
  let L := Layout.addTys slots {} (Tazuna.Smt.Expr.tys e)
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
compares its outcome with what the outcome terms denote in the model. -/

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
    accepts := Ty.down _ rfl (acceptsE.eval (G := []) () ()), resolve := Ty.down _ rfl (resolveE.eval (G := []) () ()) }

def getCode (L : Layout) : Except Refusal (QueryCode getQ) := do
  let (a, _) ← encode L (G := []) () acceptsE ()
  let (r, _) ← encode L (G := []) () resolveE ()
  pure ⟨a, r⟩

def querySvc : ServiceV :=
  { name := "s", records := recordsT, event := .int, caller := .str, init := Builtin.tableEmpty,
    apply := fun (r, _, ()) => r, subscribes := [], declares := [], commands := [], queries := [getQ], sources := [],
    machines := [], reactions := [], invariants := fun _ => [], responses := [], bounds := ⟨[], 0, 0, 0⟩,
    scenarios := [], declared := [] }

def queryLayout : Layout :=
  Layout.addTys (fun _ => 3) {} (recordsT :: .id :: Tazuna.Smt.Expr.tys acceptsE ++ Tazuna.Smt.Expr.tys resolveE)

/-- The occupied slots of a table term hold distinct keys, as a table's do. -/
def keysDistinct (d dt : Nat) (n : Nat) (t : Term) : Term :=
  let S := slotsOf d dt n 2 t
  allT ((List.range n).flatMap fun a => (List.range n).filterMap fun b =>
    if a < b then some (.not (.and (.and (S[a]!).1 (S[b]!).1) (.eq ((S[a]!).2.headD tt) ((S[b]!).2.headD tt))))
    else none)

/-- The script for one goal on the outcome terms: v0..v3 the state, v4 the caller, v5 the key, v6..v9 the outcome
terms (caller listed, the rule's holds and name, the output). -/
def queryScript (goal : List Term) : Except String (Script × QueryOut) := do
  let L := queryLayout
  let qc ← (getCode L).mapError fun r => s!"no encoding: {repr r}"
  let some ks := callerTerms L rfl getQ.callers | throw "no caller terms"
  let S := SymState.vars 0
  let (o, cond) ← (encodeQuery L getQ qc ks S.records S.now S.fresh (.var 4) (.var 5)).mapError
    fun r => s!"no encoding: {repr r}"
  let some (d, n) := L.find? recordsT | throw "no records datatype"
  let some (dt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | throw "no slot datatype"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some osrt := L.srt? (Ty.option .int) | throw "no output sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(name, holds)] := o.rules | throw "not one rule"
  pure ({ datatypes := dts, vars := [rsrt, .int, .int, .int, .str, .int, .bool, .bool, .str, osrt],
          asserts := [cond, keysDistinct d dt n S.records, .le (.int 0) S.fresh, .le (.int 0) S.nextId,
            .eq (.var 6) o.callerOk, .eq (.var 7) holds, .eq (.var 8) name, .eq (.var 9) o.output] ++ goal,
          shows := List.range 10 }, o)

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
    apply := Ty.down _ rfl (applyE.eval (G := []) () ()),
    subscribes := [⟨"x", "set", evT, Ty.down _ rfl (wrapE.eval (G := []) () ())⟩], declares := [], commands := [],
    queries := [], sources := [], machines := [], reactions := [],
    invariants := Ty.down _ rfl (invariantsE.eval (G := []) () ()), responses := [], bounds := ⟨[], 0, 0, 0⟩,
    scenarios := [], declared := [] }

def eventLayout : Layout :=
  Layout.addTys (fun _ => 3) {} (recordsT :: evT :: Tazuna.Smt.Expr.tys applyE ++ Tazuna.Smt.Expr.tys invariantsE)

def eventI : Fin eventSvc.subscribes.length := ⟨0, by decide⟩

def eventCode (L : Layout) : Except Refusal (EventCode eventSvc eventI) := do
  let (a, _) ← encode L (G := []) () applyE ()
  let (w, _) ← encode L (G := []) () wrapE ()
  let (n, _) ← encode L (G := []) () invariantsE ()
  pure ⟨a, w, n⟩

/-- v0..v3 the state, v4 the value, v5 the records after, v6 the event, v7 and v8 the invariant's holds and name. -/
def eventScript (goal : List Term) : Except String Script := do
  let L := eventLayout
  let ec ← (eventCode L).mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (o, cond) ← (encodeEvent L ec S.records (.var 4)).mapError fun r => s!"no encoding: {repr r}"
  let some (d, n) := L.find? recordsT | throw "no records datatype"
  let some (dt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | throw "no slot datatype"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some esrt := L.srt? evT | throw "no event sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(name, holds)] := o.invariants | throw "not one invariant"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, esrt, rsrt, esrt, .bool, .str],
         asserts := [cond, keysDistinct d dt n S.records, .le (.int 0) S.fresh, .le (.int 0) S.nextId,
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
  let ec ← (eventCode L).mapError fun r => s!"no encoding: {repr r}"
  let S := SymState.vars 0
  let (o, cond) ← (encodeClock L (v := eventSvc) ec.invariants S.records S.now (.var 4)).mapError
    fun r => s!"no encoding: {repr r}"
  let some (d, n) := L.find? recordsT | throw "no records datatype"
  let some (dt, _) := L.find? (.tuple [Ty.bool, .int, .int]) | throw "no slot datatype"
  let some rsrt := L.srt? recordsT | throw "no records sort"
  let some dts := L.datatypes? | throw "no datatypes"
  let [(name, holds)] := o.invariants | throw "not one invariant"
  pure { datatypes := dts, vars := [rsrt, .int, .int, .int, .int, .bool, .bool, .str],
         asserts := [cond, keysDistinct d dt n S.records, .le (.int 0) S.fresh, .le (.int 0) S.nextId,
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

def check (z3 : String) : IO Bool := do
  let solver : Solver := { path := z3, timeoutMs := 10000 }
  let mut ok := true
  for (slots, list) in [((fun _ => 3 : Ty → Nat), cases), (reslots, reslotted)] do
    for (name, ⟨t, e⟩) in list do
      match scriptOf slots e with
      | .ok (L, script) =>
        match ← solver.run script with
        | .sat vs =>
          -- The value read back decodes (T3), and codes what eval computes.
          let back := ((vs.lookup 0).bind (decodeV L t)).bind (embedV L t)
          if back.map (·.print) != (embedV L t (Expr.eval (G := []) () e ())).map (·.print) then
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
        if back.map (·.print) != (embedV L .id ((freshOf index).eval (G := []) () (step, ()))).map (·.print) then
          IO.println s!"smt-check: fresh({step}, {index}): the solver's id differs from eval's"; ok := false
      | a => IO.println s!"smt-check: fresh({step}, {index}): {repr a}"; ok := false
    | .error m => IO.println s!"smt-check: fresh({step}, {index}): {m}"; ok := false
  for (name, goal) in queryCases do
    unless ← queryCase solver name goal do ok := false
  for (name, goal) in eventCases do
    unless ← eventCase solver name goal do ok := false
  for (name, goal) in clockCases do
    unless ← clockCase solver name goal do ok := false
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
