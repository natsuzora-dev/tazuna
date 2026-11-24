import Tazuna.Semantics.Eval
import Tazuna.Smt.Slots

/-! The encoding of typed IR expressions as SMT terms. It follows `eval` clause by clause: a value of a first-order
type is coded as a term, a list (always a literal of known length) as a list of codes, and a function as a Lean
function on codes, so lambdas, calls, globals and built-ins encode the way they evaluate. Each code comes with a
condition, a Bool term that holds when no collection outgrew the slots its layout gives it; a caller states it as
the bound it checks within. Whatever has no exact encoding is refused with a reason, never approximated.

Types become sorts by a `Layout`: Int, String and Date are SMT Ints and Strings, Bool is SMT Bool, and every other
first-order type is a datatype the layout lists. `encode_agrees` (T1) proves that in every model where the condition
holds, the code denotes what `eval` computes. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- Why an expression has no encoding. -/
inductive Refusal where
  /-- A string literal holds a code point above U+2FFFF, outside SMT-LIB's strings. -/
  | unencodableString (s : String)
  /-- The expression uses a construct or type outside the fragment. -/
  | outside (what : String)
deriving Repr

/-- The datatypes a script declares: each type in the list is datatype `D<i>` by its position, with the number of
slots it holds when it is a bag or a table. -/
structure Layout where
  types : List (Ty × Nat) := []

/-- The datatype index and slot count of a type. -/
def Layout.find? (L : Layout) (t : Ty) : Option (Nat × Nat) :=
  (L.types.zipIdx.find? fun ((u, _), _) => (Ty.same u t).isSome).map fun ((_, n), d) => (d, n)

/-- Evidence that an ADT's variants are Bool's. ADT 0 is Bool in every program's type table. -/
def boolVs? : (vs : List (List Ty)) → Option (PLift (vs = [[], []]))
  | [[], []] => some ⟨rfl⟩
  | _ => none

mutual
/-- How a value of a type is coded: a term for first-order types, codes for a list literal's items, a Lean function
on codes for a function. -/
def Code : Ty → Type
  | .fn ps r => Codes ps → Except Refusal (Code r × Term)
  | .list t => List (Code t)
  | .int | .str | .tuple _ | .adt .. | .param _ | .bag _ | .table .. | .date | .id | .dsl .. => Term
def Codes : List Ty → Type
  | [] => Unit
  | t :: ts => Code t × Codes ts
end

/-- A code with its condition, or why there is none. -/
scoped notation:max "Enc " α:max => Except Refusal (α × Term)

/-- Each global's code. -/
def Encs : List Ty → Type
  | [] => Unit
  | t :: ts => Enc (Code t) × Encs ts

/-- Conjunction, leaving out a `true`. -/
def andT : Term → Term → Term
  | .bool true, b => b
  | a, .bool true => a
  | a, b => .and a b

def Code.term? : (t : Ty) → Code t → Option Term
  | .fn .., _ | .list _, _ => none
  | .int, s | .str, s | .tuple _, s | .adt .., s | .param _, s | .bag _, s | .table .., s | .date, s | .id, s
  | .dsl .., s => some s

def Code.ofTerm? : (t : Ty) → Term → Option (Code t)
  | .fn .., _ | .list _, _ => none
  | .int, s | .str, s | .tuple _, s | .adt .., s | .param _, s | .bag _, s | .table .., s | .date, s | .id, s
  | .dsl .., s => some s

def Codes.terms? : (ts : List Ty) → Codes ts → Option (List Term)
  | [], () => some []
  | t :: ts, (s, ss) => do pure ((← Code.term? t s) :: (← Codes.terms? ts ss))

def Codes.ofTerms? : (ts : List Ty) → List Term → Option (Codes ts)
  | [], [] => some ()
  | t :: ts, s :: ss => do pure ((← Code.ofTerm? t s), (← Codes.ofTerms? ts ss))
  | _, _ => none

/-- `if c then a else b` on codes of first-order types. -/
def Code.ite? (t : Ty) (c : Term) (a b : Code t) : Option (Code t) := do
  Code.ofTerm? t (.ite c (← Code.term? t a) (← Code.term? t b))

def Codes.append : {a b : List Ty} → Codes a → Codes b → Codes (a ++ b)
  | [], _, (), ys => ys
  | _ :: _, _, (x, xs), ys => (x, Codes.append xs ys)

def _root_.Tazuna.Ir.Var.code : {Γ : List Ty} → {t : Ty} → Var Γ t → Codes Γ → Code t
  | _ :: _, _, .here, (s, _) => s
  | _ :: _, _, .there v, (_, ss) => v.code ss

def _root_.Tazuna.Ir.Var.enc : {Γ : List Ty} → {t : Ty} → Var Γ t → Encs Γ → Enc (Code t)
  | _ :: _, _, .here, (s, _) => s
  | _ :: _, _, .there v, (_, ss) => v.enc ss

def absT (a : Term) : Term := .ite (.lt a (.int 0)) (.sub (.int 0) a) a

/-- Gleam's `/`: truncating, and zero for a zero divisor. SMT-LIB's `div` is Euclidean, so it divides magnitudes. -/
def tdivT (x y : Term) : Term :=
  .ite (.eq y (.int 0)) (.int 0)
    (.ite (.eq (.lt x (.int 0)) (.lt y (.int 0))) (.div (absT x) (absT y)) (.sub (.int 0) (.div (absT x) (absT y))))

/-- Gleam's `%`: the remainder takes the dividend's sign, and is zero for a zero divisor. -/
def tmodT (x y : Term) : Term :=
  .ite (.eq y (.int 0)) (.int 0)
    (.ite (.lt x (.int 0)) (.sub (.int 0) (.mod (absT x) (absT y))) (.mod (absT x) (absT y)))

end Tazuna.Smt

namespace Tazuna.Ir

mutual
/-- Whether SMT-LIB's `=` on codes is Gleam's `==`: the code of a value is unique, so no bag or table (whose slots
can hold the same items in another order) and nothing without a term. -/
def Ty.eqable : Ty → Bool
  | .int | .str | .date | .id => true
  | .tuple ts => Ty.eqables ts
  | .adt 0 _ vs => (Smt.boolVs? vs).isSome
  | .adt (_ + 1) _ vs => Ty.eqabless vs
  | .list _ | .fn .. | .param _ | .bag _ | .table .. | .dsl .. => false
def Ty.eqables : List Ty → Bool
  | [] => true
  | t :: ts => Ty.eqable t && Ty.eqables ts
def Ty.eqabless : List (List Ty) → Bool
  | [] => true
  | ts :: vs => Ty.eqables ts && Ty.eqabless vs
end

end Tazuna.Ir

namespace Tazuna.Smt

open Tazuna.Ir

def lacks (t : Ty) : Refusal := .outside s!"a type the layout lacks: {repr t}"

/-- Selects field `j` of whichever of the constructors `k`, `k + 1`, ..., `k + n` built `x`; every one of them has
the field. -/
def fieldT (d j : Nat) (x : Term) : Nat → Nat → Term
  | k, 0 => .sel d k j x
  | k, n + 1 => .ite (.is d k x) (.sel d k j x) (fieldT d j x (k + 1) n)

section
variable (L : Layout)

/-- Constructor `k` of ADT `i` with the fields' terms. -/
def adtCtor (i : Nat) (args : List Ty) (vs : List (List Ty)) (k : Nat) (fs : List Term) : Except Refusal Term :=
  match i with
  | 0 => match boolVs? vs with
    | some _ => .ok (.bool (k == 0))
    | none => .error (.outside "ADT 0 that is not Bool")
  | i + 1 => match L.find? (.adt (i + 1) args vs) with
    | some (d, _) => .ok (.ctor d k fs)
    | none => .error (lacks (.adt (i + 1) args vs))

/-- Whether `x` is constructor `k` of ADT `i`, and its fields' terms. -/
def adtView (i : Nat) (args : List Ty) (vs : List (List Ty)) (k : Nat) (x : Term) :
    Except Refusal (Term × List Term) :=
  match i with
  | 0 => match boolVs? vs with
    | some _ => .ok (if k = 0 then x else .not x, [])
    | none => .error (.outside "ADT 0 that is not Bool")
  | i + 1 => match L.find? (.adt (i + 1) args vs) with
    | some (d, _) => .ok (.is d k x, (List.range ((vs[k]?.getD []).length)).map fun j => .sel d k j x)
    | none => .error (lacks (.adt (i + 1) args vs))

def tupleD (ts : List Ty) : Except Refusal Nat :=
  match L.find? (.tuple ts) with
  | some (d, _) => .ok d
  | none => .error (lacks (.tuple ts))

def need {α : Type} (what : String) : Option α → Except Refusal α
  | some a => .ok a
  | none => .error (.outside what)

def encodeBin {a b c : Ty} : BinOp a b c → Code a → Code b → Except Refusal (Code c)
  | .add, x, y => .ok (.add x y)
  | .sub, x, y => .ok (.sub x y)
  | .mul, x, y => .ok (.mul x y)
  | .div, x, y => .ok (tdivT x y)
  | .mod, x, y => .ok (tmodT x y)
  | .lt, x, y => .ok (.lt x y)
  | .le, x, y => .ok (.le x y)
  | .gt, x, y => .ok (.lt y x)
  | .ge, x, y => .ok (.le y x)
  | .and, x, y => .ok (.and x y)
  | .or, x, y => .ok (.or x y)
  | .concat, x, y => .ok (.cat x y)
  | @BinOp.eq t _, x, y =>
    if t.eqable then do .ok (.eq (← need "==" (Code.term? t x)) (← need "==" (Code.term? t y)))
    else .error (.outside "== on this type")
  | @BinOp.ne t _, x, y =>
    if t.eqable then do .ok (.not (.eq (← need "!=" (Code.term? t x)) (← need "!=" (Code.term? t y))))
    else .error (.outside "!= on this type")

mutual
/-- Whether the value coded by `s` matches the pattern, as a Bool term, and the codes of the variables it binds. -/
def encodePat {t : Ty} {Δ : List Ty} : Pat t Δ → Code t → Except Refusal (Term × Codes Δ)
  | .wild, _ => .ok (tt, ())
  | .bind, s => .ok (tt, (s, ()))
  | .int n, s => .ok (.eq s (.int n), ())
  | .str lit, s => if inDomain lit then .ok (.eq s (.str lit), ()) else .error (.unencodableString lit)
  | @Pat.tuple ts _ ps, s => do
    let d ← tupleD L ts
    let fs ← need "a tuple item that has no term"
      (Codes.ofTerms? ts ((List.range ts.length).map fun j => .sel d 0 j s))
    encodePats ps fs
  | @Pat.ctor i args vs _ v ps, s => do
    let (m, fts) ← adtView L i args vs v.val s
    let fs ← need "a field that has no term" (Codes.ofTerms? (vs.get v) fts)
    let (m', δ) ← encodePats ps fs
    pure (andT m m', δ)
  | .as p, s => do
    let (m, δ) ← encodePat p s
    pure (m, Codes.append δ (s, ()))
def encodePats {ts : List Ty} {Δ : List Ty} : Pats ts Δ → Codes ts → Except Refusal (Term × Codes Δ)
  | .nil, () => .ok (tt, ())
  | .cons p ps, (s, ss) => do
    let (m1, δ1) ← encodePat p s
    let (m2, δ2) ← encodePats ps ss
    pure (andT m1 m2, Codes.append δ1 δ2)
end

mutual
/-- A term of the type's sort, for the items of free slots, which no value reads. -/
def defaultT : Ty → Option Term
  | .int | .date => some (.int 0)
  | .str => some (.str "")
  | .adt 0 _ vs => if (boolVs? vs).isSome then some (.bool false) else none
  | .adt (i + 1) a vs => do
    let (d, _) ← L.find? (.adt (i + 1) a vs)
    pure (.ctor d 0 (← defaultFirst vs))
  | .tuple ts => do
    let (d, _) ← L.find? (.tuple ts)
    pure (.ctor d 0 (← defaultTs ts))
  | .id => do
    let (d, _) ← L.find? .id
    pure (.ctor d 0 [.int 0])
  | .bag t => do
    let (d, n) ← L.find? (.bag t)
    let (dt, _) ← L.find? (.tuple [Ty.bool, t])
    pure (slotsTerm d dt (List.replicate n (.bool false, [← defaultT t])))
  | .table k v => do
    let (d, n) ← L.find? (.table k v)
    let (dt, _) ← L.find? (.tuple [Ty.bool, k, v])
    pure (slotsTerm d dt (List.replicate n (.bool false, [← defaultT k, ← defaultT v])))
  | .list _ | .fn .. | .param _ | .dsl .. => none
def defaultTs : List Ty → Option (List Term)
  | [] => some []
  | t :: ts => do pure ((← defaultT t) :: (← defaultTs ts))
def defaultFirst : List (List Ty) → Option (List Term)
  | [] => none
  | fs :: _ => defaultTs fs
end

/-- The datatype of a bag or table type, its slot count, and the datatype of its slots. -/
def collD (c : Ty) (item : List Ty) : Except Refusal (Nat × Nat × Nat) :=
  match L.find? c, L.find? (.tuple (Ty.bool :: item)) with
  | some (d, n), some (dt, _) => .ok (d, n, dt)
  | _, _ => .error (lacks c)

/-- `n` free slots. -/
def emptySlots (item : List Ty) (n : Nat) : Except Refusal (List Slot) := do
  let xs ← need "an item type without a default term" (item.mapM (defaultT L))
  pure (List.replicate n (.bool false, xs))

/-- A function's code applied to a slot's items. -/
def slotApply {ps : List Ty} {r : Ty} (f : Codes ps → Except Refusal (Code r × Term)) (xs : List Term) :
    Except Refusal (Code r × Term) := do
  f (← need "an item that has no term" (Codes.ofTerms? ps xs))

/-- A predicate's code applied to each slot's items: its term and its condition. -/
def slotPreds {ps : List Ty} (f : Codes ps → Except Refusal (Code Ty.bool × Term)) (S : List Slot) :
    Except Refusal (List (Term × Term)) :=
  S.mapM fun sl => slotApply f sl.2

/-- Whether a slot's key differs from `key`, as `table_remove` compares: in either direction. -/
def keepQs (key : Term) (S : List Slot) : List Term :=
  S.map fun (_, xs) => .not (.or (.eq key (xs.headD key)) (.eq (xs.headD key) key))

/-- The table's slots after `table_insert`: the key's slot freed, then the entry in the first free slot. -/
def putSlots (S : List Slot) (k v : Term) : List Slot × Term :=
  let (S', p) := insertSlots [k, v] tt (filterSlots S (keepQs k S))
  (S', .not p)

/-- The bag's slots after inserting each item in turn, with the condition that each found a free slot. -/
def insertAll : List Slot → List Term → List Slot × Term
  | S, [] => (S, tt)
  | S, x :: xs =>
    let (S', p) := insertSlots [x] tt S
    let (S'', c) := insertAll S' xs
    (S'', andT (.not p) c)

/-- The table's slots after `table_insert` of each entry in turn, with the condition that each found a slot. -/
def putAll : List Slot → List (Term × Term) → List Slot × Term
  | S, [] => (S, tt)
  | S, (k, v) :: kvs =>
    let (S', c) := putSlots S k v
    let (S'', c') := putAll S' kvs
    (S'', andT c c')

def need' {α : Type} (what : String) (b : Bool) (a : α) : Except Refusal α :=
  if b then .ok a else .error (.outside what)

/-- The code of each built-in that has an exact encoding: a table of term builders indexed by the built-in. -/
def primCode (p : Prim) (args : List Ty) (h : p.ok args = true) : Except Refusal (Code (p.ty.inst args)) :=
  match p, args, h with
  | .length, _, _ => .ok fun (s, ()) => .ok (.len s, tt)
  | .dateAddDays, _, _ => .ok fun (d, n, ()) => .ok (.add d n, tt)
  | .dateDaysBetween, _, _ => .ok fun (a, b, ()) => .ok (.sub b a, tt)
  | .require, args, _ => .ok fun (holds, rej, next, ()) => do
    let (v, c) ← next ()
    let r ← need "a rejection that has no term" (Code.term? _ rej)
    let a := (Ty.param 0).inst args
    let e := (Ty.param 1).inst args
    let err ← adtCtor L 2 [a, e] [[a], [e]] 1 [r]
    pure (.ite holds v err, .ite holds c tt)
  | .bagSize, args, _ => .ok fun (b, ()) => do
    let (d, n, dt) ← collD L (.bag ((Ty.param 0).inst args)) [(Ty.param 0).inst args]
    pure (sizeT (slotsOf d dt n 1 b), tt)
  | .bagFilter, args, _ => .ok fun (b, f, ()) => do
    let (d, n, dt) ← collD L (.bag ((Ty.param 0).inst args)) [(Ty.param 0).inst args]
    let S := slotsOf d dt n 1 b
    let R ← slotPreds f S
    pure (slotsTerm d dt (filterSlots S (R.map (·.1))), guardsT S (R.map (·.2)))
  | .bagCount, args, _ => .ok fun (b, f, ()) => do
    let (d, n, dt) ← collD L (.bag ((Ty.param 0).inst args)) [(Ty.param 0).inst args]
    let S := slotsOf d dt n 1 b
    let R ← slotPreds f S
    pure (countT S (R.map (·.1)), guardsT S (R.map (·.2)))
  | .bagAny, args, _ => .ok fun (b, f, ()) => do
    let (d, n, dt) ← collD L (.bag ((Ty.param 0).inst args)) [(Ty.param 0).inst args]
    let S := slotsOf d dt n 1 b
    let R ← slotPreds f S
    pure (anySlotT S (R.map (·.1)), guardsT S (R.map (·.2)))
  | .bagAll, args, _ => .ok fun (b, f, ()) => do
    let (d, n, dt) ← collD L (.bag ((Ty.param 0).inst args)) [(Ty.param 0).inst args]
    let S := slotsOf d dt n 1 b
    let R ← slotPreds f S
    pure (allSlotT S (R.map (·.1)), guardsT S (R.map (·.2)))
  | .bagInsert, args, _ => .ok fun (b, x, ()) => do
    let (d, n, dt) ← collD L (.bag ((Ty.param 0).inst args)) [(Ty.param 0).inst args]
    let xt ← need "an item that has no term" (Code.term? _ x)
    let (S', p) := insertSlots [xt] tt (slotsOf d dt n 1 b)
    pure (slotsTerm d dt S', .not p)
  | .tableNew, args, _ => .ok fun () => do
    let k := (Ty.param 0).inst args
    let v := (Ty.param 1).inst args
    let (d, n, dt) ← collD L (.table k v) [k, v]
    pure (slotsTerm d dt (← emptySlots L [k, v] n), tt)
  | .tableSize, args, _ => .ok fun (t, ()) => do
    let (d, n, dt) ← collD L (.table ((Ty.param 0).inst args) ((Ty.param 1).inst args))
      [(Ty.param 0).inst args, (Ty.param 1).inst args]
    pure (sizeT (slotsOf d dt n 2 t), tt)
  | .tableFilter, args, _ => .ok fun (t, f, ()) => do
    let (d, n, dt) ← collD L (.table ((Ty.param 0).inst args) ((Ty.param 1).inst args))
      [(Ty.param 0).inst args, (Ty.param 1).inst args]
    let S := slotsOf d dt n 2 t
    let R ← slotPreds f S
    pure (slotsTerm d dt (filterSlots S (R.map (·.1))), guardsT S (R.map (·.2)))
  | .tableCount, args, _ => .ok fun (t, f, ()) => do
    let (d, n, dt) ← collD L (.table ((Ty.param 0).inst args) ((Ty.param 1).inst args))
      [(Ty.param 0).inst args, (Ty.param 1).inst args]
    let S := slotsOf d dt n 2 t
    let R ← slotPreds f S
    pure (countT S (R.map (·.1)), guardsT S (R.map (·.2)))
  | .tableAny, args, _ => .ok fun (t, f, ()) => do
    let (d, n, dt) ← collD L (.table ((Ty.param 0).inst args) ((Ty.param 1).inst args))
      [(Ty.param 0).inst args, (Ty.param 1).inst args]
    let S := slotsOf d dt n 2 t
    let R ← slotPreds f S
    pure (anySlotT S (R.map (·.1)), guardsT S (R.map (·.2)))
  | .tableAll, args, _ => .ok fun (t, f, ()) => do
    let (d, n, dt) ← collD L (.table ((Ty.param 0).inst args) ((Ty.param 1).inst args))
      [(Ty.param 0).inst args, (Ty.param 1).inst args]
    let S := slotsOf d dt n 2 t
    let R ← slotPreds f S
    pure (allSlotT S (R.map (·.1)), guardsT S (R.map (·.2)))
  | .tableRemove, args, _ => .ok fun (t, key, ()) => do
    let k := (Ty.param 0).inst args
    let (d, n, dt) ← collD L (.table k ((Ty.param 1).inst args)) [k, (Ty.param 1).inst args]
    let kt ← need' "a key type whose == is not SMT-LIB's =" k.eqable (← need "a key that has no term" (Code.term? _ key))
    let S := slotsOf d dt n 2 t
    pure (slotsTerm d dt (filterSlots S (keepQs kt S)), tt)
  | .tableInsert, args, _ => .ok fun (t, key, val, ()) => do
    let k := (Ty.param 0).inst args
    let v := (Ty.param 1).inst args
    let (d, n, dt) ← collD L (.table k v) [k, v]
    let kt ← need' "a key type whose == is not SMT-LIB's =" k.eqable (← need "a key that has no term" (Code.term? _ key))
    let vt ← need "a value that has no term" (Code.term? _ val)
    let (S', c) := putSlots (slotsOf d dt n 2 t) kt vt
    pure (slotsTerm d dt S', c)
  | .bagFromList, args, _ => .ok fun (items, ()) => do
    let a := (Ty.param 0).inst args
    let (d, n, dt) ← collD L (.bag a) [a]
    let ts ← items.mapM fun x => need "an item that has no term" (Code.term? a x)
    let (S, c) := insertAll (← emptySlots L [a] n) ts
    pure (slotsTerm d dt S, c)
  | .tableFromList, args, _ => .ok fun (pairs, ()) => do
    let k := (Ty.param 0).inst args
    let v := (Ty.param 1).inst args
    let (d, n, dt) ← collD L (.table k v) [k, v]
    let dp ← need' "a key type whose == is not SMT-LIB's =" k.eqable (← tupleD L [k, v])
    let (S, c) := putAll (← emptySlots L [k, v] n) (pairs.map fun p => (.sel dp 0 0 p, .sel dp 0 1 p))
    pure (slotsTerm d dt S, c)
  | p, _, _ => .error (.outside s!"the built-in {p.sig.name}")

variable {G : List Ty} (gs : Encs G)

mutual
/-- The code of an expression whose variables have the codes `σ`, with its condition. -/
def encode {Γ : List Ty} {t : Ty} : Expr G Γ t → Codes Γ → Enc (Code t)
  | .int n, _ => .ok (.int n, tt)
  | .str s, _ => if inDomain s then .ok (.str s, tt) else .error (.unencodableString s)
  | .var v, σ => .ok (v.code σ, tt)
  | .global v, _ => v.enc gs
  | @Expr.ctor _ _ i args vs v es, σ => do
    let (ss, c) ← encodes es σ
    let fs ← need "a constructor with a field that has no term" (Codes.terms? _ ss)
    pure (← adtCtor L i args vs v.val fs, c)
  | @Expr.field _ _ i args vs ft _ k _ e, σ => do
    let (x, c) ← encode e σ
    match i with
    | 0 => .error (.outside "a field of ADT 0")
    | i + 1 => match L.find? (.adt (i + 1) args vs) with
      | some (d, _) => pure (← need "a field that has no term" (Code.ofTerm? ft (fieldT d k x 0 (vs.length - 1))), c)
      | none => .error (lacks (.adt (i + 1) args vs))
  | @Expr.index _ _ ts e k, σ => do
    let (x, c) ← encode e σ
    let d ← tupleD L ts
    pure (← need "a tuple item that has no term" (Code.ofTerm? (ts.get k) (.sel d 0 k.val x)), c)
  | @Expr.update _ _ i args fs e p, σ => do
    let (x, c) ← encode e σ
    match i with
    | 0 => .error (.outside "an update of ADT 0")
    | i + 1 => match L.find? (.adt (i + 1) args [fs]) with
      | some (d, _) =>
        let (ys, c') ← encodePatch p σ (fun j => .sel d 0 j x) 0
        pure (.ctor d 0 ys, andT c c')
      | none => .error (lacks (.adt (i + 1) args [fs]))
  | .call f args, σ => do
    let (sf, c1) ← encode f σ
    let (ss, c2) ← encodes args σ
    let (r, c3) ← sf ss
    pure (r, andT c1 (andT c2 c3))
  | .lam body, σ => .ok (fun xs => encode body (Codes.append xs σ), tt)
  | .let_ e body, σ => do
    let (s, c1) ← encode e σ
    let (r, c2) ← encode body (s, σ)
    pure (r, andT c1 c2)
  | .case e cs _, σ => do
    let (s, c1) ← encode e σ
    match ← encodeClauses cs σ s with
    | some (r, c2) => pure (r, andT c1 c2)
    | none => .error (.outside "a case without clauses")
  | .list items, σ => encodeItems items σ
  | @Expr.tuple _ _ ts es, σ => do
    let (ss, c) ← encodes es σ
    let fs ← need "a tuple with an item that has no term" (Codes.terms? _ ss)
    pure (.ctor (← tupleD L ts) 0 fs, c)
  | .bin op l r, σ => do
    let (x, c1) ← encode l σ
    let (y, c2) ← encode r σ
    pure (← encodeBin op x y, andT c1 c2)
  | .not e, σ => do
    let (x, c) ← encode e σ
    pure (.not x, c)
  | .neg e, σ => do
    let (x, c) ← encode e σ
    pure (.sub (.int 0) x, c)
  | .prim p args h, _ => do pure (← primCode L p args h, tt)
def encodes {Γ : List Ty} {ts : List Ty} : Exprs G Γ ts → Codes Γ → Enc (Codes ts)
  | .nil, _ => .ok ((), tt)
  | .cons e es, σ => do
    let (s, c1) ← encode e σ
    let (ss, c2) ← encodes es σ
    pure ((s, ss), andT c1 c2)
def encodeItems {Γ : List Ty} {t : Ty} : Items G Γ t → Codes Γ → Enc (List (Code t))
  | .nil, _ => .ok ([], tt)
  | .cons e es, σ => do
    let (s, c1) ← encode e σ
    let (ss, c2) ← encodeItems es σ
    pure (s :: ss, andT c1 c2)
/-- The terms of the updated fields, from field `j`; `keep j` is field `j` of the old value. -/
def encodePatch {Γ : List Ty} {ts : List Ty} : Patch G Γ ts → Codes Γ → (Nat → Term) → Nat → Enc (List Term)
  | .nil, _, _, _ => .ok ([], tt)
  | .keep rest, σ, keep, j => do
    let (ys, c) ← encodePatch rest σ keep (j + 1)
    pure (keep j :: ys, c)
  | @Patch.set _ _ t _ e rest, σ, keep, j => do
    let (s, c1) ← encode e σ
    let y ← need "an update with a field that has no term" (Code.term? t s)
    let (ys, c2) ← encodePatch rest σ keep (j + 1)
    pure (y :: ys, andT c1 c2)
/-- The clauses' value as a chain of `ite` over their match conditions; `none` when there is no clause. The last
clause needs no test: exhaustiveness rules out falling past it. -/
def encodeClauses {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → Codes Γ → Code t →
    Except Refusal (Option (Code r × Term))
  | .nil, _, _ => .ok none
  | .cons p body rest, σ, s => do
    let (m, δ) ← encodePat L p s
    let (vb, cb) ← encode body (Codes.append δ σ)
    match ← encodeClauses rest σ s with
    | none => pure (some (vb, cb))
    | some (vr, cr) => pure (some (← need "a case whose value has no term" (Code.ite? r m vb vr), .ite m cb cr))
  | .guarded p g body rest, σ, s => do
    let (m, δ) ← encodePat L p s
    let (vg, cg) ← encode g (Codes.append δ σ)
    let (vb, cb) ← encode body (Codes.append δ σ)
    match ← encodeClauses rest σ s with
    | none => pure (some (vb, andT cg cb))
    | some (vr, cr) =>
      pure (some (← need "a case whose value has no term" (Code.ite? r (.and m vg) vb vr),
        .ite m (andT cg (.ite vg cb cr)) cr))
end

end

/-- Each global's code, from the ones before it. -/
def _root_.Tazuna.Ir.Defs.encode (L : Layout) : {G : List Ty} → Defs G → Encs G
  | [], .nil => ()
  | _ :: _, .snoc defs _ body => let gs := defs.encode L; (Smt.encode L gs body (), gs)

/-! Layouts for scripts: the datatypes an expression meets, each after the datatypes its fields use. -/

namespace Layout

/-- The layout with `t` as its next datatype, unless it already has it. -/
def push (L : Layout) (t : Ty) (n : Nat := 0) : Layout :=
  if (L.find? t).isSome then L else { types := L.types ++ [(t, n)] }

section
variable (slots : Ty → Nat)

mutual
/-- The layout with every datatype `t` needs: its fields' types first, so each datatype refers only to earlier
ones. A bag or table gets `slots` of its type, each a tuple of an occupied flag and the item. -/
def addTy (L : Layout) : Ty → Layout
  | .tuple ts => (addTys L ts).push (.tuple ts)
  | .adt 0 a vs => if (boolVs? vs).isSome then L else (addTyss L vs).push (.adt 0 a vs)
  | .adt (i + 1) a vs => (addTyss L vs).push (.adt (i + 1) a vs)
  | .id => L.push .id
  | .list t => addTy L t
  | .fn ps r => addTy (addTys L ps) r
  | .bag t => ((addTy L t).push (.tuple [Ty.bool, t])).push (.bag t) (slots (.bag t))
  | .table k v => (((addTy (addTy L k) v)).push (.tuple [Ty.bool, k, v])).push (.table k v) (slots (.table k v))
  | .int | .str | .date | .param _ | .dsl .. => L
def addTys (L : Layout) : List Ty → Layout
  | [] => L
  | t :: ts => addTys (addTy L t) ts
def addTyss (L : Layout) : List (List Ty) → Layout
  | [] => L
  | ts :: vs => addTyss (addTys L ts) vs
end

end

/-- The sort that codes values of a first-order type. -/
def srt? (L : Layout) (t : Ty) : Option Srt :=
  match t with
  | .int | .date => some .int
  | .str => some .str
  | .adt 0 _ vs => if (boolVs? vs).isSome then some .bool else none
  | t => (L.find? t).map fun (d, _) => .dt d

/-- The declaration of a layout entry's datatype. -/
def datatype? (L : Layout) : Ty × Nat → Option Datatype
  | (.tuple ts, _) => do pure ⟨[← ts.mapM L.srt?]⟩
  | (.adt _ _ vs, _) => do pure ⟨← vs.mapM (·.mapM L.srt?)⟩
  | (.id, _) => some ⟨[[.int], [.str]]⟩
  | (.bag t, n) => do pure ⟨[List.replicate n (← L.srt? (.tuple [Ty.bool, t]))]⟩
  | (.table k v, n) => do pure ⟨[List.replicate n (← L.srt? (.tuple [Ty.bool, k, v]))]⟩
  | _ => none

def datatypes? (L : Layout) : Option (List Datatype) := L.types.mapM L.datatype?

end Layout

section
variable {G : List Ty}

mutual
/-- The type of every node of an expression, which a layout for it must cover. -/
def Expr.tys {Γ : List Ty} {t : Ty} : Expr G Γ t → List Ty
  | .ctor _ es => t :: Exprs.tys es
  | .field _ _ _ e => t :: Expr.tys e
  | .index e _ => t :: Expr.tys e
  | .update e p => t :: Expr.tys e ++ Patch.tys p
  | .call f args => t :: Expr.tys f ++ Exprs.tys args
  | .lam body => t :: Expr.tys body
  | .let_ e body => t :: Expr.tys e ++ Expr.tys body
  | @Expr.case _ _ u _ _ e cs _ => t :: u :: Expr.tys e ++ Clauses.tys cs
  | .list items => t :: Items.tys items
  | .tuple es => t :: Exprs.tys es
  | .bin _ l r => t :: Expr.tys l ++ Expr.tys r
  | .not e | .neg e => t :: Expr.tys e
  | .int _ | .str _ | .var _ | .global _ | .prim .. => [t]
def Exprs.tys {Γ : List Ty} {ts : List Ty} : Exprs G Γ ts → List Ty
  | .nil => []
  | .cons e es => Expr.tys e ++ Exprs.tys es
def Items.tys {Γ : List Ty} {t : Ty} : Items G Γ t → List Ty
  | .nil => []
  | .cons e es => Expr.tys e ++ Items.tys es
def Patch.tys {Γ : List Ty} {ts : List Ty} : Patch G Γ ts → List Ty
  | .nil => []
  | .keep rest => Patch.tys rest
  | .set e rest => Expr.tys e ++ Patch.tys rest
def Clauses.tys {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → List Ty
  | .nil => []
  | .cons _ body rest => Expr.tys body ++ Clauses.tys rest
  | .guarded _ g body rest => Expr.tys g ++ Expr.tys body ++ Clauses.tys rest
end

end

end Tazuna.Smt
