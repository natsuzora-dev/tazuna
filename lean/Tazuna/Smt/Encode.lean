import Tazuna.Semantics.Eval
import Tazuna.Smt.Slots

/-! The encoding of typed IR expressions as SMT terms. It follows `eval` clause by clause: a value of a first-order
type is coded as a term, a list too (slots in order, sized by its type's longest literal, since every list is a
literal), and a function as a Lean function on codes, so lambdas, calls, globals and built-ins encode the way they evaluate. Each code comes with a
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
slots it holds when it is a bag, a table or a list. -/
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
/-- How a value of a type is coded: a term for first-order types, a Lean function on codes for a function. A list
is a term too: slots, like a bag's, whose occupied ones hold the items in order. -/
def Code : Ty → Type
  | .fn ps r => Codes ps → Except Refusal (Code r × Term)
  | .list _ | .int | .str | .tuple _ | .adt .. | .param _ | .bag _ | .table .. | .date | .id | .dsl .. => Term
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
  | .fn .., _ => none
  | .list _, s | .int, s | .str, s | .tuple _, s | .adt .., s | .param _, s | .bag _, s | .table .., s | .date, s | .id, s
  | .dsl .., s => some s

def Code.ofTerm? : (t : Ty) → Term → Option (Code t)
  | .fn .., _ => none
  | .list _, s | .int, s | .str, s | .tuple _, s | .adt .., s | .param _, s | .bag _, s | .table .., s | .date, s | .id, s
  | .dsl .., s => some s

/-- The code shared (`Term.share`) when it is a term: a bound variable may be used any number of times. -/
def Code.share : (t : Ty) → Code t → Code t
  | .fn .., s => s
  | .list _, s | .int, s | .str, s | .tuple _, s | .adt .., s | .param _, s | .bag _, s | .table .., s | .date, s | .id, s
  | .dsl .., s => Term.share s

def Codes.share : (ts : List Ty) → Codes ts → Codes ts
  | [], () => ()
  | t :: ts, (s, ss) => (Code.share t s, Codes.share ts ss)

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
  | .int | .str | .date | .id | .dsl .fresh _ => true
  | .tuple ts => Ty.eqables ts
  | .adt 0 _ vs => (Smt.boolVs? vs).isSome
  | .adt (_ + 1) _ vs => Ty.eqabless vs
  | .list _ | .fn .. | .param _ | .bag _ | .table .. | .dsl _ _ => false
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
  | .list t => do
    let (d, n) ← L.find? (.list t)
    let (dt, _) ← L.find? (.tuple [Ty.bool, t])
    pure (slotsTerm d dt (List.replicate n (.bool false, [← defaultT t])))
  | .fn .. | .param _ | .dsl .. => none
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

/-- The collection of type `c` with items `item` holding the slots `S`, carried into its own slot count, with the
condition that they fit. -/
def collOf (c : Ty) (item : List Ty) (S : List Slot) : Except Refusal (Term × Term) := do
  let (d, n, dt) ← collD L c item
  let dflt ← need "an item type without a default term" (item.mapM (defaultT L))
  let rs := resizeSlots d dt dflt n S
  pure (slotsTerm d dt rs.1, rs.2)

/-- A function's code applied to a slot's items. -/
def slotApply {ps : List Ty} {r : Ty} (f : Codes ps → Except Refusal (Code r × Term)) (xs : List Term) :
    Except Refusal (Code r × Term) := do
  f (← need "an item that has no term" (Codes.ofTerms? ps xs))

/-- A function's code applied to each slot's items: the term of its result and its condition. -/
def slotTerms {ps : List Ty} {r : Ty} (f : Codes ps → Except Refusal (Code r × Term)) (S : List Slot) :
    Except Refusal (List (Term × Term)) :=
  S.mapM fun sl => do
    let (v, c) ← slotApply f sl.2
    pure (← need "a result that has no term" (Code.term? r v), c)

/-- Whether a slot's key differs from `key`, as `table.remove` compares: in either direction. -/
def keepQs (key : Term) (S : List Slot) : List Term :=
  S.map fun (_, xs) => .not (.or (.eq key (xs.headD key)) (.eq (xs.headD key) key))

/-- The table's slots after `table.insert`: the key's slot freed, then the entry in the first free slot. -/
def putSlots (S : List Slot) (k v : Term) : List Slot × Term :=
  let (S', p) := insertSlots [k, v] tt (filterSlots S (keepQs k S))
  (S', .not p)

def need' {α : Type} (what : String) (b : Bool) (a : α) : Except Refusal α :=
  if b then .ok a else .error (.outside what)

/-- The slots `T` where `f` holds and `S` where it does not, slot by slot. -/
def iteSlots (f : Term) (T S : List Slot) : List Slot :=
  List.zipWith (fun a b => (.ite f a.1 b.1, List.zipWith (.ite f) a.2 b.2)) T S

/-- The table's slots after `table.insert` of each pair a list's slots hold, occupied ones in order, shared after each
insertion, with the condition that each found a slot. `dp` is the pairs' datatype. -/
def putFrom (d dt dp : Nat) : List Slot → List Slot → List Slot × Term
  | S, [] => (S, tt)
  | S, (f, xs) :: P =>
    let (S', c) := putSlots S (.sel dp 0 0 (xs.headD tt)) (.sel dp 0 1 (xs.headD tt))
    let T := iteSlots f S' S
    let (S'', c') := putFrom d dt dp (slotsOf d dt T.length 2 (slotsTerm d dt T)) P
    (S'', andT (.ite f c tt) c')

/-- A list literal: its items in the first slots of the list's datatype, the others free, with the condition that
they fit. -/
def listOf (t : Ty) (items : List Term) : Except Refusal (Term × Term) := do
  let (d, n, dt) ← collD L (.list t) [t]
  let dflt ← need "an item type without a default term" (defaultT L t)
  if items.length ≤ n then
    pure (slotsTerm d dt (items.map (tt, [·]) ++ List.replicate (n - items.length) (.bool false, [dflt])), tt)
  else pure (slotsTerm d dt [], .bool false)

/-- Whether each slot's key is `key`. -/
def hitQs (key : Term) (S : List Slot) : List Term := S.map fun sl => .eq key (sl.2.headD key)

/-- A lookup of `key` in a table's slots: whether an occupied slot has the key, and the value of the first that has
it (`dv` when none has). A table's keys are unique, so the first is the only one, whatever the slots' order. -/
def lookupT (key dv : Term) (S : List Slot) : Term × Term :=
  (anySlotT S (hitQs key S), pickT dv (List.zipWith (fun sl q => (sl.1, q, sl.2.getD 1 dv)) S (hitQs key S)))

/-- The table's slots and the lookup of the key's code in them. -/
def lookupCode (k v : Ty) (t key : Term) : Except Refusal (Term × Term) := do
  let (d, n, dt) ← collD L (.table k v) [k, v]
  let kt ← need' "a key type whose == is not SMT-LIB's =" k.eqable key
  let dv ← need "a value type without a default term" (defaultT L v)
  pure (lookupT kt dv (slotsOf d dt n 2 t))

/-- How often `x` occurs among the occupied slots' items, by SMT-LIB's `=`. -/
def countEqT (x : Term) (S : List Slot) : Term := countT S (S.map fun sl => .eq x (sl.2.headD x))

/-- `==` on bags: as many items, and each item of the first occurs as often in the second. -/
def bagEqT (A B : List Slot) : Term :=
  .and (.eq (sizeT A) (sizeT B))
    (allSlotT A (A.map fun sl => .eq (countEqT (sl.2.headD tt) A) (countEqT (sl.2.headD tt) B)))

/-- `==` on tables: as many entries, and each key of the first has an equal value in the second. -/
def tableEqT (dv : Term) (A B : List Slot) : Term :=
  .and (.eq (sizeT A) (sizeT B))
    (allSlotT A (A.map fun sl =>
      .and (lookupT (sl.2.headD dv) dv B).1 (.eq (sl.2.getD 1 dv) (lookupT (sl.2.headD dv) dv B).2)))

/-- Gleam's `==`: SMT-LIB's `=` where codes are unique, and multiset or map equality over the slots of bags and
tables, whose slots can hold the same items in another order. -/
def eqCode (t : Ty) (x y : Code t) : Except Refusal Term :=
  if t.eqable then do .ok (.eq (← need "==" (Code.term? t x)) (← need "==" (Code.term? t y)))
  else match t, x, y with
    | .bag a, x, y => do
      let (d, n, dt) ← collD L (.bag a) [a]
      need' "== on a bag whose items' == is not SMT-LIB's =" a.eqable (bagEqT (slotsOf d dt n 1 x) (slotsOf d dt n 1 y))
    | .table k v, x, y => do
      let (d, n, dt) ← collD L (.table k v) [k, v]
      let dv ← need "a value type without a default term" (defaultT L v)
      need' "== on a table whose keys' or values' == is not SMT-LIB's =" (k.eqable && v.eqable)
        (tableEqT dv (slotsOf d dt n 2 x) (slotsOf d dt n 2 y))
    | _, _, _ => .error (.outside "== on this type")

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
  | @BinOp.eq t _, x, y => eqCode L t x y
  | @BinOp.ne t _, x, y => do .ok (.not (← eqCode L t x y))

/-- `bag.min_by` (`lt` is `<`) or `bag.max_by` (`lt` is `>`) of the bag `b` by the key function `f`: the item of
the occupied slot whose key beats every other occupied slot's, `Tie` when none does and a slot is occupied, `Empty`
when none is. A slot wins when its own key is the only one among the occupied slots that fails to beat it. -/
def pickCode (lt : Term → Term → Term) (a : Ty) (b : Term) (f : Codes [a] → Except Refusal (Code .int × Term)) :
    Except Refusal (Term × Term) := do
  let (d, n, dt) ← collD L (.bag a) [a]
  let S := slotsOf d dt n 1 b
  let R ← slotTerms f S
  let ks := R.map fun r => Term.share r.1
  let ws := ks.map fun k => Term.share (.eq (countT S (ks.map fun k' => .not (lt k k'))) (.int 1))
  let dv ← need "an item type without a default term" (defaultT L a)
  let found ← adtCtor L 2 [a, Ty.pickError] [[a], [Ty.pickError]] 0
    [pickT dv (List.zipWith (fun sl w => (sl.1, w, sl.2.headD dv)) S ws)]
  let tie ← adtCtor L 2 [a, Ty.pickError] [[a], [Ty.pickError]] 1 [← adtCtor L 4 [] [[], []] 1 []]
  let empty ← adtCtor L 2 [a, Ty.pickError] [[a], [Ty.pickError]] 1 [← adtCtor L 4 [] [[], []] 0 []]
  pure (.ite (anySlotT S ws) found (.ite (anySlotT S (S.map fun _ => tt)) tie empty), guardsT S (R.map (·.2)))

/-- `fresh(source, index)`'s number: the Cantor pairing of the step's counter and the index, as `freshId` computes
it, with the index made a natural number (`2 * index`, or `2 * -index - 1` below zero). -/
def freshT (step index : Term) : Term :=
  let i := Term.share (.ite (.le (.int 0) index) (.mul (.int 2) index) (.sub (.mul (.int 2) (.sub (.int 0) index)) (.int 1)))
  let a := Term.share (.add step i)
  .add (.div (.mul a (.add a (.int 1))) (.int 2)) i

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
    let R ← slotTerms f S
    pure (slotsTerm d dt (filterSlots S (R.map (·.1))), guardsT S (R.map (·.2)))
  | .bagCount, args, _ => .ok fun (b, f, ()) => do
    let (d, n, dt) ← collD L (.bag ((Ty.param 0).inst args)) [(Ty.param 0).inst args]
    let S := slotsOf d dt n 1 b
    let R ← slotTerms f S
    pure (countT S (R.map (·.1)), guardsT S (R.map (·.2)))
  | .bagSum, args, _ => .ok fun (b, f, ()) => do
    let (d, n, dt) ← collD L (.bag ((Ty.param 0).inst args)) [(Ty.param 0).inst args]
    let S := slotsOf d dt n 1 b
    let R ← slotTerms f S
    pure (sumSlotT S (R.map (·.1)), guardsT S (R.map (·.2)))
  | .bagMap, args, _ => .ok fun (b, f, ()) => do
    let (d, n, dt) ← collD L (.bag ((Ty.param 0).inst args)) [(Ty.param 0).inst args]
    let S := slotsOf d dt n 1 b
    let R ← slotTerms f S
    let (r, c) ← collOf L (.bag ((Ty.param 1).inst args)) [(Ty.param 1).inst args]
      (mapSlots (fun _ q => [q]) S (R.map (·.1)))
    pure (r, andT (guardsT S (R.map (·.2))) c)
  | .bagAny, args, _ => .ok fun (b, f, ()) => do
    let (d, n, dt) ← collD L (.bag ((Ty.param 0).inst args)) [(Ty.param 0).inst args]
    let S := slotsOf d dt n 1 b
    let R ← slotTerms f S
    pure (anySlotT S (R.map (·.1)), guardsT S (R.map (·.2)))
  | .bagAll, args, _ => .ok fun (b, f, ()) => do
    let (d, n, dt) ← collD L (.bag ((Ty.param 0).inst args)) [(Ty.param 0).inst args]
    let S := slotsOf d dt n 1 b
    let R ← slotTerms f S
    pure (allSlotT S (R.map (·.1)), guardsT S (R.map (·.2)))
  | .bagInsert, args, _ => .ok fun (b, x, ()) => do
    let (d, n, dt) ← collD L (.bag ((Ty.param 0).inst args)) [(Ty.param 0).inst args]
    let xt ← need "an item that has no term" (Code.term? _ x)
    let (S', p) := insertSlots [xt] tt (slotsOf d dt n 1 b)
    pure (slotsTerm d dt S', .not p)
  | .bagContains, args, _ => .ok fun (b, x, ()) => do
    let a := (Ty.param 0).inst args
    let (d, n, dt) ← collD L (.bag a) [a]
    let xt ← need' "an item type whose == is not SMT-LIB's =" a.eqable (← need "an item that has no term" (Code.term? _ x))
    let S := slotsOf d dt n 1 b
    pure (anySlotT S (S.map fun sl => .eq xt (sl.2.headD xt)), tt)
  | .bagMinBy, args, _ => .ok fun (b, f, ()) => pickCode L (fun k k' => .lt k k') ((Ty.param 0).inst args) b f
  | .bagMaxBy, args, _ => .ok fun (b, f, ()) => pickCode L (fun k k' => .lt k' k) ((Ty.param 0).inst args) b f
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
    let R ← slotTerms f S
    pure (slotsTerm d dt (filterSlots S (R.map (·.1))), guardsT S (R.map (·.2)))
  | .tableMap, args, _ => .ok fun (t, f, ()) => do
    let k := (Ty.param 0).inst args
    let (d, n, dt) ← collD L (.table k ((Ty.param 1).inst args)) [k, (Ty.param 1).inst args]
    let S := slotsOf d dt n 2 t
    let R ← slotTerms f S
    let (r, c) ← collOf L (.table k ((Ty.param 2).inst args)) [k, (Ty.param 2).inst args]
      (mapSlots (fun xs q => [xs.headD q, q]) S (R.map (·.1)))
    pure (r, andT (guardsT S (R.map (·.2))) c)
  | .tableKeys, args, _ => .ok fun (t, ()) => do
    let k := (Ty.param 0).inst args
    let (d, n, dt) ← collD L (.table k ((Ty.param 1).inst args)) [k, (Ty.param 1).inst args]
    let S := slotsOf d dt n 2 t
    collOf L (.bag k) [k] (mapSlots (fun xs q => [xs.headD q]) S (S.map fun _ => tt))
  | .tableValues, args, _ => .ok fun (t, ()) => do
    let v := (Ty.param 1).inst args
    let (d, n, dt) ← collD L (.table ((Ty.param 0).inst args) v) [(Ty.param 0).inst args, v]
    let S := slotsOf d dt n 2 t
    collOf L (.bag v) [v] (mapSlots (fun xs q => [xs.getD 1 q]) S (S.map fun _ => tt))
  | .tableCount, args, _ => .ok fun (t, f, ()) => do
    let (d, n, dt) ← collD L (.table ((Ty.param 0).inst args) ((Ty.param 1).inst args))
      [(Ty.param 0).inst args, (Ty.param 1).inst args]
    let S := slotsOf d dt n 2 t
    let R ← slotTerms f S
    pure (countT S (R.map (·.1)), guardsT S (R.map (·.2)))
  | .tableAny, args, _ => .ok fun (t, f, ()) => do
    let (d, n, dt) ← collD L (.table ((Ty.param 0).inst args) ((Ty.param 1).inst args))
      [(Ty.param 0).inst args, (Ty.param 1).inst args]
    let S := slotsOf d dt n 2 t
    let R ← slotTerms f S
    pure (anySlotT S (R.map (·.1)), guardsT S (R.map (·.2)))
  | .tableAll, args, _ => .ok fun (t, f, ()) => do
    let (d, n, dt) ← collD L (.table ((Ty.param 0).inst args) ((Ty.param 1).inst args))
      [(Ty.param 0).inst args, (Ty.param 1).inst args]
    let S := slotsOf d dt n 2 t
    let R ← slotTerms f S
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
    let (dl, nl, dt) ← collD L (.list a) [a]
    collOf L (.bag a) [a] (slotsOf dl dt nl 1 items)
  | .tableFromList, args, _ => .ok fun (pairs, ()) => do
    let k := (Ty.param 0).inst args
    let v := (Ty.param 1).inst args
    let (d, n, dt) ← collD L (.table k v) [k, v]
    let (dl, nl, dtl) ← collD L (.list (.tuple [k, v])) [.tuple [k, v]]
    let dp ← need' "a key type whose == is not SMT-LIB's =" k.eqable (← tupleD L [k, v])
    let (S, c) := putFrom d dt dp (← emptySlots L [k, v] n) (slotsOf dl dtl nl 1 pairs)
    pure (slotsTerm d dt S, c)
  | .tableGet, args, _ => .ok fun (t, key, ()) => do
    let v := (Ty.param 1).inst args
    let kt ← need "a key that has no term" (Code.term? _ key)
    let (hit, found) ← lookupCode L ((Ty.param 0).inst args) v t kt
    pure (.ite hit (← adtCtor L 3 [v] [[v], []] 0 [found]) (← adtCtor L 3 [v] [[v], []] 1 []), tt)
  | .tableLookup, args, _ => .ok fun (t, key, rej, next, ()) => do
    let kt ← need "a key that has no term" (Code.term? _ key)
    let (hit, found) ← lookupCode L ((Ty.param 0).inst args) ((Ty.param 1).inst args) t kt
    let fc ← need "a value that has no term" (Code.ofTerm? ((Ty.param 1).inst args) found)
    let (r, c) ← next (fc, ())
    let rt ← need "a rejection that has no term" (Code.term? _ rej)
    let a := (Ty.param 2).inst args
    let e := (Ty.param 3).inst args
    pure (.ite hit r (← adtCtor L 2 [a, e] [[a], [e]] 1 [rt]), .ite hit c tt)
  | .fresh, _, _ => .ok fun (step, index, ()) => do
    let (d, _) ← need "a layout without Id" (L.find? .id)
    pure (.ctor d 0 [freshT step index], tt)
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
    let (r, c3) ← sf (Codes.share _ ss)
    pure (r, andT c1 (andT c2 c3))
  | .lam body, σ => .ok (fun xs => encode body (Codes.append xs σ), tt)
  | .let_ e body, σ => do
    let (s, c1) ← encode e σ
    let (r, c2) ← encode body (Code.share _ s, σ)
    pure (r, andT c1 c2)
  | .case e cs _, σ => do
    let (s, c1) ← encode e σ
    match ← encodeClauses cs σ (Code.share _ s) with
    | some (r, c2) => pure (r, andT c1 c2)
    | none => .error (.outside "a case without clauses")
  | @Expr.list _ _ t items, σ => do
    let (ss, c1) ← encodeItems items σ
    let ts ← ss.mapM fun s => need "a list item that has no term" (Code.term? t s)
    let (r, c2) ← listOf L t ts
    pure (r, andT c1 c2)
  | @Expr.tuple _ _ ts es, σ => do
    let (ss, c) ← encodes es σ
    let fs ← need "a tuple with an item that has no term" (Codes.terms? _ ss)
    pure (.ctor (← tupleD L ts) 0 fs, c)
  | .bin op l r, σ => do
    let (x, c1) ← encode l σ
    let (y, c2) ← encode r σ
    pure (← encodeBin L op x y, andT c1 c2)
  | .not e, σ => do
    let (x, c) ← encode e σ
    pure (.not x, c)
  | .neg e, σ => do
    let (x, c) ← encode e σ
    pure (.sub (.int 0) x, c)
  | .prim p args h, _ => do pure (← primCode L p args h, tt)
  | .close .., _ => .error (.outside "a function a structure value keeps")
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
ones. A bag, table or list gets `slots` of its type, each a tuple of an occupied flag and the item. -/
def addTy (L : Layout) : Ty → Layout
  | .tuple ts => (addTys L ts).push (.tuple ts)
  | .adt 0 a vs => if (boolVs? vs).isSome then L else (addTyss L vs).push (.adt 0 a vs)
  | .adt (i + 1) a vs => (addTyss L vs).push (.adt (i + 1) a vs)
  | .id => L.push .id
  | .list t => ((addTy L t).push (.tuple [Ty.bool, t])).push (.list t) (slots (.list t))
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
  | .int | .date | .dsl .fresh _ => some .int
  | .str => some .str
  | .adt 0 _ vs => if (boolVs? vs).isSome then some .bool else none
  | t => (L.find? t).map fun (d, _) => .dt d

/-- The declaration of a layout entry's datatype. -/
def datatype? (L : Layout) : Ty × Nat → Option Datatype
  | (.tuple ts, _) => do pure ⟨[← ts.mapM L.srt?]⟩
  | (.adt _ _ vs, _) => do pure ⟨← vs.mapM (·.mapM L.srt?)⟩
  | (.id, _) => some ⟨[[.int], [.str]]⟩
  | (.bag t, n) | (.list t, n) => do pure ⟨[List.replicate n (← L.srt? (.tuple [Ty.bool, t]))]⟩
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
  | .close _ env _ _ body => t :: Exprs.tys env ++ Expr.tys body
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

section
variable {G : List Ty}

mutual
/-- The type and length of every list literal of an expression. Every list is a literal, so a list type's longest
literal bounds every list of that type: its slot count, derived, with no bound to state. -/
def Expr.lits {Γ : List Ty} {t : Ty} : Expr G Γ t → List (Ty × Nat)
  | .list items => (t, Items.len items) :: Items.lits items
  | .ctor _ es | .tuple es => Exprs.lits es
  | .field _ _ _ e | .index e _ | .lam e | .not e | .neg e => Expr.lits e
  | .update e p => Expr.lits e ++ Patch.lits p
  | .call f args => Expr.lits f ++ Exprs.lits args
  | .let_ e body | .bin _ e body => Expr.lits e ++ Expr.lits body
  | .case e cs _ => Expr.lits e ++ Clauses.lits cs
  | .close _ env _ _ body => Exprs.lits env ++ Expr.lits body
  | .int _ | .str _ | .var _ | .global _ | .prim .. => []
def Exprs.lits {Γ : List Ty} {ts : List Ty} : Exprs G Γ ts → List (Ty × Nat)
  | .nil => []
  | .cons e es => Expr.lits e ++ Exprs.lits es
def Items.lits {Γ : List Ty} {t : Ty} : Items G Γ t → List (Ty × Nat)
  | .nil => []
  | .cons e es => Expr.lits e ++ Items.lits es
def Items.len {Γ : List Ty} {t : Ty} : Items G Γ t → Nat
  | .nil => 0
  | .cons _ es => Items.len es + 1
def Patch.lits {Γ : List Ty} {ts : List Ty} : Patch G Γ ts → List (Ty × Nat)
  | .nil => []
  | .keep rest => Patch.lits rest
  | .set e rest => Expr.lits e ++ Patch.lits rest
def Clauses.lits {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → List (Ty × Nat)
  | .nil => []
  | .cons _ body rest => Expr.lits body ++ Clauses.lits rest
  | .guarded _ g body rest => Expr.lits g ++ Expr.lits body ++ Clauses.lits rest
end

end

/-- The slot count of each type: a list's longest literal among `lits`, and `base` for bags and tables. -/
def listSlots (base : Ty → Nat) (lits : List (Ty × Nat)) : Ty → Nat
  | .list t => lits.foldl (fun m (u, k) => if (Ty.same u (.list t)).isSome then max m k else m) 0
  | t => base t

end Tazuna.Smt
