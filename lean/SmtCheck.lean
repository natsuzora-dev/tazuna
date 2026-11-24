import Tazuna.Smt.EncodeThm
import Tazuna.Smt.Solver

/-! Runs the solver on printed scripts and reads its answers back: the theorems cover printing and reading our own
text, and this check covers what only the solver can say, that it reads the text as SMT-LIB and prints values the
reader reads. Each case encodes a closed expression, asks the solver for a variable equal to it, and compares the
value with `eval`. Usage: smt-check <z3 executable>. -/

open Tazuna.Ir Tazuna.Smt

abbrev E (t : Ty) := Expr [] [] t

mutual
/-- The SMT value that codes a value, as `RelV` relates them. -/
def valOf (L : Layout) : (t : Ty) → t.den → Option Val
  | .int, n => some (.int n)
  | .str, s => some (.str s)
  | .date, n => some (.int n)
  | .id, x => (L.find? .id).map fun (d, _) => idVal d x
  | .adt 0 _ vs, x => (boolVs? vs).map fun ⟨h⟩ => .bool (altsBool (h ▸ x))
  | .adt (i + 1) a vs, x => do let (d, _) ← L.find? (.adt (i + 1) a vs); valAlts L d 0 vs x
  | .tuple ts, x => do let (d, _) ← L.find? (.tuple ts); pure (.ctor d 0 (← valsOf L ts x))
  | .list _, _ | .fn .., _ | .param _, _ | .bag _, _ | .table .., _ | .dsl .., _ => none
def valsOf (L : Layout) : (ts : List Ty) → Ty.dens ts → Option (List Val)
  | [], _ => some []
  | t :: ts, (x, xs) => do pure ((← valOf L t x) :: (← valsOf L ts xs))
def valAlts (L : Layout) (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Ty.alts vs → Option Val
  | k, fs :: _, .inl x => do pure (.ctor d k (← valsOf L fs x))
  | k, _ :: vs, .inr y => valAlts L d (k + 1) vs y
end

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

/-- `bag_from_list([1, 2, 2])` -/
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
def isTwo : Expr [] [.int] Ty.bool := .bin (.eq rfl) (.var .here) (.int 2)
def bigger : Expr [] [.int] Ty.bool := .bin .gt (.var .here) (.int 1)
/-- `table_from_list([#(1, "a"), #(1, "c")])`: the last pair for key 1 wins. -/
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
/-- `table_map(t, fn(k, v) { v <> "!" })` -/
def tableBang (t : E (.table .int .str)) : E (.table .int .str) :=
  .call (.prim .tableMap [.int, .str, .str] rfl)
    (.cons t (.cons (.lam (.bin .concat (.var (.there .here)) (.str "!"))) .nil))
/-- `bag_from_list([1, 5])` -/
def b2 : E (.bag .int) :=
  .call (.prim .bagFromList [.int] rfl) (.cons (.list (.cons (.int 1) (.cons (.int 5) .nil))) .nil)

def tableGet (t : E (.table .int .str)) (k : Int) : E (Ty.option .str) :=
  .call (.prim .tableGet [.int, .str] rfl) (.cons t (.cons (.int k) .nil))
/-- `use v <- ref(t, k, "no")` continuing with `Ok(v)`. -/
def refOk (t : E (.table .int .str)) (k : Int) : E (Ty.result .str .str) :=
  .call (.prim .ref [.int, .str, .str, .str] rfl) (.cons t (.cons (.int k) (.cons (.str "no")
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

def check (z3 : String) : IO Bool := do
  let solver : Solver := { path := z3, timeoutMs := 10000 }
  let mut ok := true
  for (slots, list) in [((fun _ => 3 : Ty → Nat), cases), (reslots, reslotted)] do
    for (name, ⟨t, e⟩) in list do
      match scriptOf slots e with
      | .ok (L, script) =>
        match ← solver.run script with
        | .sat vs =>
          if (vs.lookup 0).map (·.print) != (valOf L t (Expr.eval (G := []) () e ())).map (·.print) then
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
