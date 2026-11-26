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

/-- A construct a spec can write that the fragment leaves out. -/
inductive Limit where
  /-- A value of the type is a function or a handle where the encoding needs a term. -/
  | function (t : Ty)
  /-- Gleam's `==` on the type is not SMT-LIB's `=` (a bag or a table compares its slots in their order). -/
  | equality (t : Ty)
  /-- A handle, command or query named by an expression that is no literal. -/
  | dynamicName
  | builtin (name : String)
  /-- A kept function whose result is effects. -/
  | effectClosure
  /-- A value of the type holds a type variable or a structure value (a service, a machine), which have no sort. -/
  | unsortable (t : Ty)
  /-- A value the spec writes of the type (a listed caller, a machine's initial state) holds a collection with more
  items than the type's slots: a bound is below it. -/
  | slots (t : Ty)
  /-- Two own steps whose orders differ with each keeping the names it made sent more requests than the search for
  a renaming of their wire ids takes (`wireSearchCap`), so whether the orders end the same is not known. Never an
  encoder's refusal: prove reads it from a pair's counterexample. -/
  | renamings (sends : Nat)
  /-- Two own steps whose orders end with the same data up to renaming keep different functions (by site or captured
  values), and what functions do is not compared, so whether the orders end the same is not known. Never an encoder's
  refusal: prove reads it from a pair's counterexample. -/
  | keptFunctions
  /-- A value of the type, written or decoded as a whole, holds a table whose key is no plain value, so its
  well-formedness (distinct keys) has no term. -/
  | tableKey (t : Ty)
deriving Repr

/-- What a layout lacks that an encoding needs. A layout built for the program has none of these. -/
inductive LayoutGap where
  /-- The datatype of the type, a datatype a default or a constant of it needs, or slots for a constant of it. -/
  | type (t : Ty)
  /-- A variant of the effect datatype for the kind of effect, or a pending shape or external for it. -/
  | effectKind (name : String)
  /-- An instance table with fewer slots than its machine's instance bag. -/
  | instanceSlots (t : Ty)
deriving Repr

/-- A case the program's types rule out but the IR's do not. -/
inductive Unexpected where
  /-- A value of a type the step itself codes (the state, an input, a context, a captured value) is a function: check
  and the loader keep functions out of those types. -/
  | function (t : Ty)
  /-- ADT 0, which every program's type table declares as Bool, with other variants. -/
  | adtZero
  | emptyCase
deriving Repr

/-- Why an expression has no encoding: a limit of the fragment the spec reached, a gap in the layout, or a case the
program's types rule out. -/
inductive Refusal where
  /-- A string literal holds a code point above U+2FFFF, outside SMT-LIB's strings. -/
  | unencodableString (s : String)
  | limit (l : Limit)
  | layout (g : LayoutGap)
  | unexpected (u : Unexpected)
deriving Repr

/-- An encoder's terms with its two conditions: `cond`, what the terms ask of the values (exact against the step's
`Fits`), and `codes`, what the codes built at captured values ask, which holds wherever those values are the program's. -/
structure Encoded (α : Type) where
  out : α
  cond : Term
  codes : Term

/-- What a kept function's code says of it: where it is written and the types of the values it captured. -/
structure SiteKey where
  site : SiteId
  Γ : List Ty

/-- One kind of effect a program writes: a request to the external command (with a rejection type) or query `name`
of these types, from the event type `event`, whose `on_answer` and (for a query) `ensures` are written at these
sites. An effect of the kind is coded by its variant of the effect datatype, whose fields are what varies: the input
and the values each site captured. -/
structure EffectKey where
  event : Ty
  name : String
  input : Ty
  output : Ty
  rejection : Option Ty
  ensures : Option SiteKey
  answer : SiteKey

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
/-- The types of what varies among the effects of a kind. -/
def EffectKey.fields (k : EffectKey) : List Ty :=
  [k.input, .tuple ((k.ensures.map (·.Γ)).getD []), .tuple k.answer.Γ]

/-- One kind of effect that runs a command or query of the service's own: its name, the types of its caller and
input, its rejection (a command) or output (a query), and the site of its `on_answer`, from the event type `event`.
An effect of the kind is coded by its variant of the effect datatype, after the request kinds' variants; its fields
are the caller, the input and the values the site captured. -/
inductive OwnKey where
  | command (event : Ty) (name : String) (caller input rejection : Ty) (answer : SiteKey)
  | query (event : Ty) (name : String) (caller input output : Ty) (answer : SiteKey)

def OwnKey.event : OwnKey → Ty
  | .command e .. | .query e .. => e

def OwnKey.name : OwnKey → String
  | .command _ n .. | .query _ n .. => n

def OwnKey.answer : OwnKey → SiteKey
  | .command _ _ _ _ _ a | .query _ _ _ _ _ a => a

/-- The types of what varies among the effects of a kind. -/
def OwnKey.fields : OwnKey → List Ty
  | .command _ _ c i _ a | .query _ _ c i _ a => [c, i, .tuple a.Γ]

/-- The datatypes a script declares: each type in the list is datatype `D<i>` by its position, with the number of
slots it holds when it is a bag, a table or a list. `effects` and `owns` list the kinds of effect values the script
codes: the type `Effect(event)` is a datatype with one variant per kind of that event type, requests first. -/
structure Layout where
  types : List (Ty × Nat) := []
  effects : List EffectKey := []
  owns : List OwnKey := []

/-- The request kinds of effect of the event type `e`, in the order of their variants. -/
def Layout.effectsOf (L : Layout) (e : Ty) : List EffectKey := L.effects.filter fun k => (Ty.same k.event e).isSome

/-- The own kinds of effect of the event type `e`, in the order of their variants, after the request kinds'. -/
def Layout.ownsOf (L : Layout) (e : Ty) : List OwnKey := L.owns.filter fun k => (Ty.same k.event e).isSome

/-- The fields of every variant of the effect datatype of the event type `e`. -/
def Layout.effectFields (L : Layout) (e : Ty) : List (List Ty) :=
  (L.effectsOf e).map (·.fields) ++ (L.ownsOf e).map (·.fields)

def SiteKey.same (a b : SiteKey) : Bool := a.site == b.site && (Ty.sames a.Γ b.Γ).isSome

def optSame {α : Type} (f : α → α → Bool) : Option α → Option α → Bool
  | none, none => true
  | some a, some b => f a b
  | _, _ => false

/-- Whether two kinds of effect are the same kind. -/
def EffectKey.same (a b : EffectKey) : Bool :=
  (Ty.same a.event b.event).isSome && a.name == b.name && (Ty.same a.input b.input).isSome &&
    (Ty.same a.output b.output).isSome && optSame (fun x y => (Ty.same x y).isSome) a.rejection b.rejection &&
    optSame SiteKey.same a.ensures b.ensures && a.answer.same b.answer

def OwnKey.same : OwnKey → OwnKey → Bool
  | .command e n c i j a, .command e' n' c' i' j' a' | .query e n c i j a, .query e' n' c' i' j' a' =>
    (Ty.same e e').isSome && n == n' && (Ty.same c c').isSome && (Ty.same i i').isSome && (Ty.same j j').isSome &&
      a.same a'
  | _, _ => false

/-- The datatype index and slot count of a type. -/
def Layout.find? (L : Layout) (t : Ty) : Option (Nat × Nat) :=
  (L.types.zipIdx.find? fun ((u, _), _) => (Ty.same u t).isSome).map fun ((_, n), d) => (d, n)

/-- Evidence that an ADT's variants are Bool's. ADT 0 is Bool in every program's type table. -/
def boolVs? : (vs : List (List Ty)) → Option (PLift (vs = [[], []]))
  | [[], []] => some ⟨rfl⟩
  | _ => none

/-- A kept function's code: where it is written, the types of the values it captured, and their terms. It is static,
so an effect that holds it names the site in its variant (defunctionalization in the encoder). -/
structure ClosureCode where
  key : SiteKey
  env : List Term

/-- How a value of a structure type is coded: a kept function by its closure code, a handle to an external's command
by its name and to an external's query by its name and its `ensures`, an own command or query by its name, all
static; anything else by a term. -/
def DslCode : Dsl → List Ty → Type
  | .closure, _ => ClosureCode
  | .externalCommand, _ | .command, _ | .query, _ => String
  | .externalQuery, _ => String × ClosureCode
  | .spec, _ | .service, _ | .machine, _ | .reaction, _ | .external, _ | .source, _
  | .declared, _ | .effect, _ | .subscription, _ | .bounds, _ | .create, _ | .response, _ | .scenario, _ | .step, _
  | .sender, _ | .fresh, _ | .effectClosure, _ => Term

mutual
/-- How a value of a type is coded: a term for first-order types, a Lean function on codes for a function. A list
is a term too: slots, like a bag's, whose occupied ones hold the items in order. -/
def Code : Ty → Type
  | .fn ps r => Codes ps → Except Refusal (Code r × Term)
  | .dsl k a => DslCode k a
  | .list _ | .int | .str | .tuple _ | .adt .. | .param _ | .bag _ | .table .. | .date | .id => Term
def Codes : List Ty → Type
  | [] => Unit
  | t :: ts => Code t × Codes ts
end

/-- The term of a structure value's code, when it has one. -/
def DslCode.term? : (k : Dsl) → (a : List Ty) → DslCode k a → Option Term
  | .closure, _, _ | .externalCommand, _, _ | .externalQuery, _, _ | .command, _, _ | .query, _, _ => none
  | .spec, _, s | .service, _, s | .machine, _, s | .reaction, _, s | .external, _, s
  | .source, _, s | .declared, _, s | .effect, _, s | .subscription, _, s | .bounds, _, s | .create, _, s
  | .response, _, s | .scenario, _, s | .step, _, s | .sender, _, s | .fresh, _, s | .effectClosure, _, s => some s

def DslCode.ofTerm? : (k : Dsl) → (a : List Ty) → Term → Option (DslCode k a)
  | .closure, _, _ | .externalCommand, _, _ | .externalQuery, _, _ | .command, _, _ | .query, _, _ => none
  | .spec, _, s | .service, _, s | .machine, _, s | .reaction, _, s | .external, _, s
  | .source, _, s | .declared, _, s | .effect, _, s | .subscription, _, s | .bounds, _, s | .create, _, s
  | .response, _, s | .scenario, _, s | .step, _, s | .sender, _, s | .fresh, _, s | .effectClosure, _, s => some s

def DslCode.share : (k : Dsl) → (a : List Ty) → DslCode k a → DslCode k a
  | .closure, _, s | .externalCommand, _, s | .externalQuery, _, s | .command, _, s | .query, _, s => s
  | .spec, _, s | .service, _, s | .machine, _, s | .reaction, _, s | .external, _, s
  | .source, _, s | .declared, _, s | .effect, _, s | .subscription, _, s | .bounds, _, s | .create, _, s
  | .response, _, s | .scenario, _, s | .step, _, s | .sender, _, s | .fresh, _, s | .effectClosure, _, s => Term.share s

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
  | .dsl k a, s => DslCode.term? k a s
  | .list _, s | .int, s | .str, s | .tuple _, s | .adt .., s | .param _, s | .bag _, s | .table .., s | .date, s | .id, s =>
    some s

def Code.ofTerm? : (t : Ty) → Term → Option (Code t)
  | .fn .., _ => none
  | .dsl k a, s => DslCode.ofTerm? k a s
  | .list _, s | .int, s | .str, s | .tuple _, s | .adt .., s | .param _, s | .bag _, s | .table .., s | .date, s | .id, s =>
    some s

/-- The code shared (`Term.share`) when it is a term: a bound variable may be used any number of times. -/
def Code.share : (t : Ty) → Code t → Code t
  | .fn .., s => s
  | .dsl k a, s => DslCode.share k a s
  | .list _, s | .int, s | .str, s | .tuple _, s | .adt .., s | .param _, s | .bag _, s | .table .., s | .date, s | .id, s =>
    Term.share s

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
/-- Whether the type has an SMT sort: data with no function or type variable inside and ADT 0 only as Bool, an effect
of such an event type, or a fresh-id source. The program's types include those of the spec's structure (lists of declarations, services);
those values are never coded, so they get no datatype. -/
def Ty.sorted : Ty → Bool
  | .int | .str | .date | .id => true
  | .param _ | .fn .. => false
  | .list t | .bag t => Ty.sorted t
  | .tuple ts => Ty.sorteds ts
  | .adt 0 _ vs => (Smt.boolVs? vs).isSome
  | .adt (_ + 1) _ vs => Ty.sortedss vs
  | .table k v => Ty.sorted k && Ty.sorted v
  | .dsl .effect [e] => Ty.sorted e
  | .dsl k _ => k == .fresh
def Ty.sorteds : List Ty → Bool
  | [] => true
  | t :: ts => Ty.sorted t && Ty.sorteds ts
def Ty.sortedss : List (List Ty) → Bool
  | [] => true
  | ts :: vs => Ty.sorteds ts && Ty.sortedss vs
end

mutual
/-- Whether every datatype of the type has an SMT sort: a function's parameters and result have theirs, any other
type has a sort. A function is coded by a Lean function, so it needs no sort of its own. -/
def Ty.sortable : Ty → Bool
  | .fn ps r => Ty.sortables ps && Ty.sortable r
  | t => t.sorted
def Ty.sortables : List Ty → Bool
  | [] => true
  | t :: ts => Ty.sortable t && Ty.sortables ts
end


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

mutual
/-- Data with a sort is comparable: a sort rules out functions and type variables, data rules out structure values. -/
theorem Ty.comparable_of_sorted : (t : Ty) → t.sorted = true → t.isData = true → t.comparable = true
  | .int, _, _ | .str, _, _ | .date, _, _ | .id, _, _ | .param _, _, _ => rfl
  | .fn .., h, _ => by simp [Ty.sorted] at h
  | .list t, h, hd | .bag t, h, hd =>
    Ty.comparable_of_sorted t (by simpa [Ty.sorted] using h) (by simpa [Ty.isData] using hd)
  | .table k v, h, hd => by
    simp only [Ty.sorted, Ty.isData, Bool.and_eq_true] at h hd
    simp [Ty.comparable, Ty.comparable_of_sorted k h.1 hd.1, Ty.comparable_of_sorted v h.2 hd.2]
  | .tuple ts, h, hd => Ty.comparables_of_sorteds ts h hd
  | .adt 0 _ vs, h, _ => by
    simp only [Ty.sorted] at h
    unfold Smt.boolVs? at h
    split at h
    · rfl
    · simp at h
  | .adt (_ + 1) _ vs, h, hd => Ty.comparabless_of_sortedss vs h hd
  | .dsl k _, _, hd => by simpa [Ty.comparable, Ty.isData] using hd
theorem Ty.comparables_of_sorteds : (ts : List Ty) → Ty.sorteds ts = true → Ty.isDatas ts = true →
    Ty.comparables ts = true
  | [], _, _ => rfl
  | t :: ts, h, hd => by
    simp only [Ty.sorteds, Ty.isDatas, Bool.and_eq_true] at h hd
    simp [Ty.comparables, Ty.comparable_of_sorted t h.1 hd.1, Ty.comparables_of_sorteds ts h.2 hd.2]
theorem Ty.comparabless_of_sortedss : (vs : List (List Ty)) → Ty.sortedss vs = true → Ty.isDatass vs = true →
    Ty.comparabless vs = true
  | [], _, _ => rfl
  | ts :: vs, h, hd => by
    simp only [Ty.sortedss, Ty.isDatass, Bool.and_eq_true] at h hd
    simp [Ty.comparabless, Ty.comparables_of_sorteds ts h.1 hd.1, Ty.comparabless_of_sortedss vs h.2 hd.2]
end

end Tazuna.Ir

namespace Tazuna.Smt

open Tazuna.Ir

/-- The layout lacks the datatype of `t`: a gap when `t` has a sort, else the limit that it has none. -/
def lacks (t : Ty) : Refusal := if t.sorted then .layout (.type t) else .limit (.unsortable t)

/-- The layout lacks the kind of effect with these fields: a gap when they are data with sorts, else the limit. -/
def lacksKind (name : String) (fields : List Ty) : Refusal :=
  if !(Ty.tuple fields).isData then .limit (.function (.tuple fields))
  else if Ty.sorteds fields then .layout (.effectKind name) else .limit (.unsortable (.tuple fields))

section
variable (L : Layout)

/-- Every datatype of the layout has a sort, so a type it finds has one, and every kind of effect's fields are data
with sorts. -/
structure SortedLayout : Prop where
  types : ∀ p ∈ L.types, p.1.sorted = true
  effects : ∀ k ∈ L.effects, Ty.sorteds k.fields = true ∧ (Ty.tuple k.fields).isData = true
  owns : ∀ k ∈ L.owns, Ty.sorteds k.fields = true ∧ (Ty.tuple k.fields).isData = true

end

/-- An own kind's fields in a sorted layout are comparable, so a model's value of them decodes wherever it codes
data (`decode_of_relV`). -/
theorem SortedLayout.ownsComparable {L : Layout} (hL : SortedLayout L) {e : Ty} {k : OwnKey} (hk : k ∈ L.ownsOf e) :
    ∀ t ∈ k.fields, t.comparable = true := by
  have h := hL.owns k (List.mem_filter.1 hk).1
  exact comparables_mem (Ty.comparables_of_sorteds _ h.1 (by simpa [Ty.isData] using h.2))
where
  comparables_mem : {ts : List Ty} → Ty.comparables ts = true → ∀ t ∈ ts, t.comparable = true
    | [], _, _, ht => by cases ht
    | _ :: _, hc, _, ht => by
      simp only [Ty.comparables, Bool.and_eq_true] at hc
      rcases List.mem_cons.1 ht with rfl | ht
      · exact hc.1
      · exact comparables_mem hc.2 _ ht

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
    | none => .error (.unexpected .adtZero)
  | i + 1 => match L.find? (.adt (i + 1) args vs) with
    | some (d, _) => .ok (.ctor d k fs)
    | none => .error (lacks (.adt (i + 1) args vs))

/-- Whether `x` is constructor `k` of ADT `i`, and its fields' terms. -/
def adtView (i : Nat) (args : List Ty) (vs : List (List Ty)) (k : Fin vs.length) (x : Term) :
    Except Refusal (Term × List Term) :=
  match i with
  | 0 => match boolVs? vs with
    | some _ => .ok (if k.val = 0 then x else .not x, [])
    | none => .error (.unexpected .adtZero)
  | i + 1 => match L.find? (.adt (i + 1) args vs) with
    | some (d, _) => .ok (.is d k x, (List.range (vs.get k).length).map fun j => .sel d k j x)
    | none => .error (lacks (.adt (i + 1) args vs))

def tupleD (ts : List Ty) : Except Refusal Nat :=
  match L.find? (.tuple ts) with
  | some (d, _) => .ok d
  | none => .error (lacks (.tuple ts))

def need {α : Type} (r : Refusal) : Option α → Except Refusal α
  | some a => .ok a
  | none => .error r

/-- The datatype index and slot count of a type, refused when the layout lacks it. -/
abbrev Layout.findE (L : Layout) (t : Ty) : Except Refusal (Nat × Nat) := need (lacks t) (L.find? t)

/-- The term of a code, refused at a type whose values are functions or handles. -/
abbrev Code.termE (t : Ty) (c : Code t) : Except Refusal Term := need (.limit (.function t)) (Code.term? t c)

/-- The code of a term at the type `t`, refused when `t`'s values are functions or handles. -/
abbrev Code.ofTermE (t : Ty) (x : Term) : Except Refusal (Code t) := need (.limit (.function t)) (Code.ofTerm? t x)

/-- The term of a code at a type the step itself codes, which holds no function. -/
abbrev Code.dataTermE (t : Ty) (c : Code t) : Except Refusal Term := need (.unexpected (.function t)) (Code.term? t c)

/-- The code of a term at a type the step itself codes, which holds no function. -/
abbrev Code.ofDataE (t : Ty) (x : Term) : Except Refusal (Code t) := need (.unexpected (.function t)) (Code.ofTerm? t x)

mutual
/-- Whether the value coded by `s` matches the pattern, as a Bool term, and the codes of the variables it binds. -/
def encodePat {t : Ty} {Δ : List Ty} : Pat t Δ → Code t → Except Refusal (Term × Codes Δ)
  | .wild, _ => .ok (tt, ())
  | .bind, s => .ok (tt, (s, ()))
  | .int n, s => .ok (.eq s (.int n), ())
  | .str lit, s => if inDomain lit then .ok (.eq s (.str lit), ()) else .error (.unencodableString lit)
  | @Pat.tuple ts _ ps, s => do
    let d ← tupleD L ts
    let fs ← need (.limit (.function (.tuple ts)))
      (Codes.ofTerms? ts ((List.range ts.length).map fun j => .sel d 0 j s))
    encodePats ps fs
  | @Pat.ctor i args vs _ v ps, s => do
    let (m, fts) ← adtView L i args vs v s
    let fs ← need (.limit (.function (.tuple (vs.get v)))) (Codes.ofTerms? (vs.get v) fts)
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

section
variable (dsl : Dsl → List Ty → Option Term)

mutual
/-- A term of the type's sort, with `dsl` giving one for a structure type. -/
def defaultWith : Ty → Option Term
  | .int | .date => some (.int 0)
  | .str => some (.str "")
  | .adt 0 _ vs => if (boolVs? vs).isSome then some (.bool false) else none
  | .adt (i + 1) a vs => do
    let (d, _) ← L.find? (.adt (i + 1) a vs)
    pure (.ctor d 0 (← firstWith vs))
  | .tuple ts => do
    let (d, _) ← L.find? (.tuple ts)
    pure (.ctor d 0 (← defaultsWith ts))
  | .id => do
    let (d, _) ← L.find? .id
    pure (.ctor d 0 [.int 0, .int 0])
  | .bag t => do
    let (d, n) ← L.find? (.bag t)
    let (dt, _) ← L.find? (.tuple [Ty.bool, t])
    pure (slotsTerm d dt (List.replicate n (.bool false, ⟨[← defaultWith t], rfl⟩)))
  | .table k v => do
    let (d, n) ← L.find? (.table k v)
    let (dt, _) ← L.find? (.tuple [Ty.bool, k, v])
    pure (slotsTerm d dt (List.replicate n (.bool false, ⟨[← defaultWith k, ← defaultWith v], rfl⟩)))
  | .list t => do
    let (d, n) ← L.find? (.list t)
    let (dt, _) ← L.find? (.tuple [Ty.bool, t])
    pure (slotsTerm d dt (List.replicate n (.bool false, ⟨[← defaultWith t], rfl⟩)))
  | .dsl k a => dsl k a
  | .fn .. | .param _ => none
def defaultsWith : List Ty → Option (List Term)
  | [] => some []
  | t :: ts => do pure ((← defaultWith t) :: (← defaultsWith ts))
def firstWith : List (List Ty) → Option (List Term)
  | [] => some []
  | fs :: _ => defaultsWith fs
end

end

/-- A fresh-id source's term of its counter's sort; no other structure type has one. -/
def freshDefault : Dsl → List Ty → Option Term
  | .fresh, _ => some (.int 0)
  | _, _ => none

/-- A value of the effect datatype of the event type `e`: its first kind with a term of each field's sort, or the
datatype's one constructor when no kind exists. -/
def effectDefault (e : Ty) : Option Term := do
  let (d, _) ← L.find? (.dsl .effect [e])
  match (L.effectFields e).head? with
  | none => pure (.ctor d 0 [])
  | some fs => pure (.ctor d 0 (← fs.mapM (defaultWith L freshDefault)))

/-- A term of the type's sort, for the items of free slots, which no value reads. An effect has one too, any value
of its datatype, so a list of effects has free slots; a fresh-id source has its counter's, an Int. -/
def defaultT : Ty → Option Term :=
  defaultWith L fun
    | .effect, [e] => effectDefault L e
    | .fresh, _ => some (.int 0)
    | _, _ => none

/-- The term of a value of `t` that free slots hold, refused when the layout lacks a datatype it needs. -/
abbrev defaultE (t : Ty) : Except Refusal Term := need (lacks t) (defaultT L t)

/-- The datatype of a bag or table type, its slot count, and the datatype of its slots. -/
def collD (c : Ty) (item : List Ty) : Except Refusal (Nat × Nat × Nat) :=
  match L.find? c, L.find? (.tuple (Ty.bool :: item)) with
  | some (d, n), some (dt, _) => .ok (d, n, dt)
  | _, _ => .error (lacks c)

theorem mapM_some_length {α β : Type} (g : α → Option β) : (xs : List α) → (ys : List β) → xs.mapM g = some ys →
    ys.length = xs.length
  | [], ys, h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; rfl
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    cases hx : g x with
    | none => simp [hx, bind, Option.bind] at h
    | some y =>
      cases hxs : xs.mapM g with
      | none => simp [hx, hxs, bind, Option.bind] at h
      | some ys' =>
        simp only [hx, hxs, bind, Option.bind, pure, Option.some.injEq] at h
        subst h
        simp [mapM_some_length g xs ys' hxs]

/-- A term of each item type, for the items of free slots. -/
def defaultItems (item : List Ty) : Except Refusal (SlotItems item.length) :=
  match h : item.mapM (defaultT L) with
  | some xs => .ok ⟨xs, mapM_some_length _ _ _ h⟩
  | none => .error (lacks (.tuple item))

/-- `n` free slots. -/
def emptySlots (item : List Ty) (n : Nat) : Except Refusal (List (Slot item.length)) := do
  pure (List.replicate n (.bool false, ← defaultItems L item))

/-- The collection of type `c` with items `item` holding the slots `S`, carried into its own slot count, with the
condition that they fit. -/
def collOf (c : Ty) (item : List Ty) (S : List (Slot item.length)) : Except Refusal (Term × Term) := do
  let (d, n, dt) ← collD L c item
  let dflt ← defaultItems L item
  let rs := resizeSlots d dt dflt n S
  pure (slotsTerm d dt rs.1, rs.2)

/-- A function's code applied to a slot's items. -/
def slotApply {ps : List Ty} {r : Ty} {w : Nat} (f : Codes ps → Except Refusal (Code r × Term)) (xs : SlotItems w) :
    Except Refusal (Code r × Term) := do
  f (← need (.limit (.function (.tuple ps))) (Codes.ofTerms? ps xs.1))

/-- A function's code applied to each slot's items: the term of its result and its condition. -/
def slotTerms {ps : List Ty} {r : Ty} {w : Nat} (f : Codes ps → Except Refusal (Code r × Term)) (S : List (Slot w)) :
    Except Refusal (List (Term × Term)) :=
  S.mapM fun sl => do
    let (v, c) ← slotApply f sl.2
    pure (← Code.termE r v, c)

/-- Whether a slot's key differs from `key`, as `table.remove` compares: in either direction. -/
def keepQs (key : Term) (S : List (Slot 2)) : List Term :=
  S.map fun (_, xs) => .not (.or (.eq key xs[0]) (.eq xs[0] key))

/-- The table's slots after `table.insert`: the key's slot freed, then the entry in the first free slot. -/
def putSlots (S : List (Slot 2)) (k v : Term) : List (Slot 2) × Term :=
  let (S', p) := insertSlots ⟨[k, v], rfl⟩ tt (filterSlots S (keepQs k S))
  (S', .not p)

def need' {α : Type} (r : Refusal) (b : Bool) (a : α) : Except Refusal α :=
  if b then .ok a else .error r

/-- The slots `T` where `f` holds and `S` where it does not, slot by slot. -/
def iteSlots {w : Nat} (f : Term) (T S : List (Slot w)) : List (Slot w) :=
  List.zipWith (fun a b => (.ite f a.1 b.1, ⟨List.zipWith (.ite f) a.2.1 b.2.1, by simp [a.2.2, b.2.2]⟩)) T S

/-- The table's slots after `table.insert` of each pair a list's slots hold, occupied ones in order, shared after each
insertion, with the condition that each found a slot. `dp` is the pairs' datatype. -/
def putFrom (d dt dp : Nat) : List (Slot 2) → List (Slot 1) → List (Slot 2) × Term
  | S, [] => (S, tt)
  | S, (f, xs) :: P =>
    let (S', c) := putSlots S (.sel dp 0 0 xs[0]) (.sel dp 0 1 xs[0])
    let T := iteSlots f S' S
    let (S'', c') := putFrom d dt dp (slotsOf d dt T.length 2 (slotsTerm d dt T)) P
    (S'', andT (.ite f c tt) c')

/-- A list literal: its items in the first slots of the list's datatype, the others free, with the condition that
they fit. -/
def listOf (t : Ty) (items : List Term) : Except Refusal (Term × Term) := do
  let (d, n, dt) ← collD L (.list t) [t]
  let dflt ← defaultE L t
  if items.length ≤ n then
    pure (slotsTerm d dt (items.map (tt, ⟨[·], rfl⟩) ++ List.replicate (n - items.length) (.bool false, ⟨[dflt], rfl⟩)), tt)
  else pure (slotsTerm (w := 1) d dt [], .bool false)

/-- Whether each slot's key is `key`. -/
def hitQs (key : Term) (S : List (Slot 2)) : List Term := S.map fun sl => .eq key sl.2[0]

/-- A lookup of `key` in a table's slots: whether an occupied slot has the key, and the value of the first that has
it (`dv` when none has). A table's keys are unique, so the first is the only one, whatever the slots' order. -/
def lookupT (key dv : Term) (S : List (Slot 2)) : Term × Term :=
  (anySlotT S (hitQs key S), pickT dv (List.zipWith (fun sl q => (sl.1, q, sl.2[1])) S (hitQs key S)))

/-- The table's slots and the lookup of the key's code in them. -/
def lookupCode (k v : Ty) (t key : Term) : Except Refusal (Term × Term) := do
  let (d, n, dt) ← collD L (.table k v) [k, v]
  let kt ← need' (.limit (.equality k)) k.eqable key
  let dv ← defaultE L v
  pure (lookupT kt dv (slotsOf d dt n 2 t))

/-- How often `x` occurs among the occupied slots' items, by the item equality `eq`. -/
def countEqT (eq : Term → Term → Term) (x : Term) (S : List (Slot 1)) : Term := countT S (S.map fun sl => eq x sl.2[0])

/-- `==` on bags: as many items, and each item of the first occurs as often in the second. -/
def bagEqT (eq : Term → Term → Term) (A B : List (Slot 1)) : Term :=
  .and (.eq (sizeT A) (sizeT B))
    (allSlotT A (A.map fun sl => .eq (countEqT eq sl.2[0] A) (countEqT eq sl.2[0] B)))

/-- `==` on tables: as many entries, and each key of the first has a value in the second that `eq` finds equal. -/
def tableEqT (eq : Term → Term → Term) (dv : Term) (A B : List (Slot 2)) : Term :=
  .and (.eq (sizeT A) (sizeT B))
    (allSlotT A (A.map fun sl =>
      .and (lookupT sl.2[0] dv B).1 (eq sl.2[1] (lookupT sl.2[0] dv B).2)))

/-- `==` on fields `j`, `j + 1`, ... of constructor `k` of datatype `d`, each by its own equality. -/
def fieldsEqT (d k : Nat) : Nat → List (Term → Term → Term) → Term → Term → Term
  | _, [], _, _ => tt
  | j, f :: fs, x, y => .and (f (.sel d k j x) (.sel d k j y)) (fieldsEqT d k (j + 1) fs x y)

/-- `==` on a custom type whose variants are constructors `k`, `k + 1`, ... of datatype `d`: the same constructor
with equal fields. -/
def altsEqT (d : Nat) : Nat → List (List (Term → Term → Term)) → Term → Term → Term
  | _, [], _, _ => .bool false
  | k, fs :: vs, x, y =>
    .or (.and (.is d k x) (.and (.is d k y) (fieldsEqT d k 0 fs x y))) (altsEqT d (k + 1) vs x y)

mutual
/-- Gleam's `==` on two terms of the type: SMT-LIB's `=` where codes are unique, multiset or map equality over the
slots of bags and tables, whose slots can hold the same items in another order, and field by field through tuples
and custom types that hold them. A list's free slots may sit between occupied ones, so its code is not unique and
its `==` is refused. -/
def eqFn : Ty → Except Refusal (Term → Term → Term)
  | .int | .str | .date | .id => .ok .eq
  | .dsl k a => if k == .fresh then .ok .eq else .error (.limit (.equality (.dsl k a)))
  | .adt 0 a vs => if (boolVs? vs).isSome then .ok .eq else .error (.limit (.equality (.adt 0 a vs)))
  | .tuple ts => if Ty.eqables ts then .ok .eq else do
    let d ← tupleD L ts
    let fs ← eqFns ts
    pure fun x y => fieldsEqT d 0 0 fs x.share y.share
  | .adt (i + 1) a vs => if Ty.eqabless vs then .ok .eq else do
    let (d, _) ← L.findE (.adt (i + 1) a vs)
    let fss ← eqFnss vs
    pure fun x y => altsEqT d 0 fss x.share y.share
  | .bag a => do
    let (d, n, dt) ← collD L (.bag a) [a]
    let f ← eqFn a
    pure fun x y => bagEqT f (slotsOf d dt n 1 x) (slotsOf d dt n 1 y)
  | .table k v => do
    let (d, n, dt) ← collD L (.table k v) [k, v]
    let dv ← defaultE L v
    let f ← eqFn v
    need' (.limit (.equality (.table k v))) k.eqable fun x y => tableEqT f dv (slotsOf d dt n 2 x) (slotsOf d dt n 2 y)
  | t@(.list _) | t@(.fn ..) | t@(.param _) => .error (.limit (.equality t))
def eqFns : List Ty → Except Refusal (List (Term → Term → Term))
  | [] => .ok []
  | t :: ts => do pure ((← eqFn t) :: (← eqFns ts))
def eqFnss : List (List Ty) → Except Refusal (List (List (Term → Term → Term)))
  | [] => .ok []
  | ts :: vs => do pure ((← eqFns ts) :: (← eqFnss vs))
end

/-- Gleam's `==` on two codes. -/
def eqCode (t : Ty) (x y : Code t) : Except Refusal Term := do
  let f ← eqFn L t
  pure (f (← Code.termE t x) (← Code.termE t y))

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
  let dv ← defaultE L a
  let found ← adtCtor L 2 [a, Ty.pickError] [[a], [Ty.pickError]] 0
    [pickT dv (List.zipWith (fun sl w => (sl.1, w, sl.2[0])) S ws)]
  let tie ← adtCtor L 2 [a, Ty.pickError] [[a], [Ty.pickError]] 1 [← adtCtor L 4 [] [[], []] 1 []]
  let empty ← adtCtor L 2 [a, Ty.pickError] [[a], [Ty.pickError]] 1 [← adtCtor L 4 [] [[], []] 0 []]
  pure (.ite (anySlotT S ws) found (.ite (anySlotT S (S.map fun _ => tt)) tie empty), guardsT S (R.map (·.2)))

-- No `ensures` site means no captured values: the empty list is the meaning, not a fallback.
set_option linter.tazuna.silentDefault false in
/-- An effect of the kind `key`: its variant of the effect datatype, with the input and the terms of the values the
`ensures` and `on_answer` sites captured. -/
def effectT (key : EffectKey) (input : Term) (ens answer : List Term) : Except Refusal Term := do
  let (d, _) ← L.findE (.dsl .effect [key.event])
  let k ← need (lacksKind key.name key.fields) ((L.effectsOf key.event).findIdx? (·.same key))
  let de ← tupleD L ((key.ensures.map (·.Γ)).getD [])
  let da ← tupleD L key.answer.Γ
  pure (.ctor d k [input, .ctor de 0 ens, .ctor da 0 answer])

/-- An effect of the own kind `key`: its variant of the effect datatype, after the request kinds', with the caller,
the input and the terms of the values the `on_answer` site captured. -/
def ownT (key : OwnKey) (caller input : Term) (answer : List Term) : Except Refusal Term := do
  let (d, _) ← L.findE (.dsl .effect [key.event])
  let k ← need (lacksKind key.name key.fields) ((L.ownsOf key.event).findIdx? (·.same key))
  let da ← tupleD L key.answer.Γ
  pure (.ctor d ((L.effectsOf key.event).length + k) [caller, input, .ctor da 0 answer])

/-- The code of each built-in that has an exact encoding: a table of term builders indexed by the built-in. -/
def primCode (p : Prim) (args : List Ty) (h : p.ok args = true) : Except Refusal (Code (p.ty.inst args)) :=
  match p, args, h with
  | .length, _, _ => .ok fun (s, ()) => .ok (.len s, tt)
  | .dateAddDays, _, _ => .ok fun (d, n, ()) => .ok (.add d n, tt)
  | .dateDaysBetween, _, _ => .ok fun (a, b, ()) => .ok (.sub b a, tt)
  | .require, args, _ => .ok fun (holds, rej, next, ()) => do
    let (v, c) ← next ()
    let r ← Code.termE _ rej
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
      (mapSlots (fun _ q => ⟨[q], rfl⟩) S (R.map (·.1)))
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
    let xt ← Code.termE _ x
    let (S', p) := insertSlots ⟨[xt], rfl⟩ tt (slotsOf d dt n 1 b)
    pure (slotsTerm d dt S', .not p)
  | .bagContains, args, _ => .ok fun (b, x, ()) => do
    let a := (Ty.param 0).inst args
    let (d, n, dt) ← collD L (.bag a) [a]
    let xt ← need' (.limit (.equality a)) a.eqable (← Code.termE _ x)
    let S := slotsOf d dt n 1 b
    pure (anySlotT S (S.map fun sl => .eq xt sl.2[0]), tt)
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
      (mapSlots (fun xs q => ⟨[xs[0], q], rfl⟩) S (R.map (·.1)))
    pure (r, andT (guardsT S (R.map (·.2))) c)
  | .tableKeys, args, _ => .ok fun (t, ()) => do
    let k := (Ty.param 0).inst args
    let (d, n, dt) ← collD L (.table k ((Ty.param 1).inst args)) [k, (Ty.param 1).inst args]
    let S := slotsOf d dt n 2 t
    collOf L (.bag k) [k] (mapSlots (fun xs _ => ⟨[xs[0]], rfl⟩) S (S.map fun _ => tt))
  | .tableValues, args, _ => .ok fun (t, ()) => do
    let v := (Ty.param 1).inst args
    let (d, n, dt) ← collD L (.table ((Ty.param 0).inst args) v) [(Ty.param 0).inst args, v]
    let S := slotsOf d dt n 2 t
    collOf L (.bag v) [v] (mapSlots (fun xs _ => ⟨[xs[1]], rfl⟩) S (S.map fun _ => tt))
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
    let kt ← need' (.limit (.equality k)) k.eqable (← Code.termE _ key)
    let S := slotsOf d dt n 2 t
    pure (slotsTerm d dt (filterSlots S (keepQs kt S)), tt)
  | .tableInsert, args, _ => .ok fun (t, key, val, ()) => do
    let k := (Ty.param 0).inst args
    let v := (Ty.param 1).inst args
    let (d, n, dt) ← collD L (.table k v) [k, v]
    let kt ← need' (.limit (.equality k)) k.eqable (← Code.termE _ key)
    let vt ← Code.termE _ val
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
    let dp ← need' (.limit (.equality k)) k.eqable (← tupleD L [k, v])
    let (S, c) := putFrom d dt dp (← emptySlots L [k, v] n) (slotsOf dl dtl nl 1 pairs)
    pure (slotsTerm d dt S, c)
  | .tableGet, args, _ => .ok fun (t, key, ()) => do
    let v := (Ty.param 1).inst args
    let kt ← Code.termE _ key
    let (hit, found) ← lookupCode L ((Ty.param 0).inst args) v t kt
    pure (.ite hit (← adtCtor L 3 [v] [[v], []] 0 [found]) (← adtCtor L 3 [v] [[v], []] 1 []), tt)
  | .tableLookup, args, _ => .ok fun (t, key, rej, next, ()) => do
    let kt ← Code.termE _ key
    let (hit, found) ← lookupCode L ((Ty.param 0).inst args) ((Ty.param 1).inst args) t kt
    let fc ← Code.ofTermE ((Ty.param 1).inst args) found
    let (r, c) ← next (fc, ())
    let rt ← Code.termE _ rej
    let a := (Ty.param 2).inst args
    let e := (Ty.param 3).inst args
    pure (.ite hit r (← adtCtor L 2 [a, e] [[a], [e]] 1 [rt]), .ite hit c tt)
  | .fresh, _, _ => .ok fun (step, index, ()) => do
    let (d, _) ← L.findE .id
    pure (.ctor d 0 [step, index], tt)
  | .externalCommand, _, _ => .ok fun (name, ()) => match name with
    | .str n => .ok (n, tt)
    | _ => .error (.limit .dynamicName)
  | .externalQuery, _, _ => .ok fun (name, ens, ()) => match name with
    | .str n => .ok ((n, ens), tt)
    | _ => .error (.limit .dynamicName)
  | .requestCommand, args, _ => .ok fun (name, input, oa, ()) => do
    let it ← Code.termE _ input
    let key : EffectKey := ⟨(Ty.param 0).inst args, name, (Ty.param 1).inst args, (Ty.param 2).inst args,
      some ((Ty.param 3).inst args), none, oa.key⟩
    pure (← effectT L key it [] oa.env, tt)
  | .requestQuery, args, _ => .ok fun ((name, ens), input, oa, ()) => do
    let it ← Code.termE _ input
    let key : EffectKey := ⟨(Ty.param 0).inst args, name, (Ty.param 1).inst args, (Ty.param 2).inst args, none,
      some ens.key, oa.key⟩
    pure (← effectT L key it ens.env oa.env, tt)
  | .command, _, _ => .ok fun (name, _, _, _, _, ()) => match name with
    | .str n => .ok (n, tt)
    | _ => .error (.limit .dynamicName)
  | .query, _, _ => .ok fun (name, _, _, _, ()) => match name with
    | .str n => .ok (n, tt)
    | _ => .error (.limit .dynamicName)
  | .sendCommand, args, _ => .ok fun (name, caller, input, oa, ()) => do
    let ct ← Code.termE _ caller
    let it ← Code.termE _ input
    let key : OwnKey := .command ((Ty.param 1).inst args) name ((Ty.param 2).inst args) ((Ty.param 3).inst args)
      ((Ty.param 4).inst args) oa.key
    pure (← ownT L key ct it oa.env, tt)
  | .sendQuery, args, _ => .ok fun (name, caller, input, oa, ()) => do
    let ct ← Code.termE _ caller
    let it ← Code.termE _ input
    let key : OwnKey := .query ((Ty.param 1).inst args) name ((Ty.param 2).inst args) ((Ty.param 3).inst args)
      ((Ty.param 4).inst args) oa.key
    pure (← ownT L key ct it oa.env, tt)
  | p, _, _ => .error (.limit (.builtin p.sig.name))

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
    let fs ← need (.limit (.function (.tuple (vs.get v)))) (Codes.terms? _ ss)
    pure (← adtCtor L i args vs v.val fs, c)
  | @Expr.field _ _ i args vs ft _ k _ e, σ => do
    let (x, c) ← encode e σ
    match i with
    | 0 => .error (.unexpected .adtZero)
    | i + 1 => match L.find? (.adt (i + 1) args vs) with
      | some (d, _) => pure (← Code.ofTermE ft (fieldT d k x 0 (vs.length - 1)), c)
      | none => .error (lacks (.adt (i + 1) args vs))
  | @Expr.index _ _ ts e k, σ => do
    let (x, c) ← encode e σ
    let d ← tupleD L ts
    pure (← Code.ofTermE (ts.get k) (.sel d 0 k.val x), c)
  | @Expr.update _ _ i args fs e p, σ => do
    let (x, c) ← encode e σ
    match i with
    | 0 => .error (.unexpected .adtZero)
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
    | none => .error (.unexpected .emptyCase)
  | @Expr.list _ _ t items, σ => do
    let (ss, c1) ← encodeItems items σ
    let ts ← ss.mapM fun s => Code.termE t s
    let (r, c2) ← listOf L t ts
    pure (r, andT c1 c2)
  | @Expr.tuple _ _ ts es, σ => do
    let (ss, c) ← encodes es σ
    let fs ← need (.limit (.function (.tuple ts))) (Codes.terms? _ ss)
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
  | @Expr.close _ _ Γ' _ site env _ _ _, σ => do
    let (ss, c) ← encodes env σ
    let ts ← need (.limit (.function (.tuple Γ'))) (Codes.terms? _ ss)
    pure (⟨⟨site, Γ'⟩, ts⟩, c)
  | .closeEffect .., _ => .error (.limit .effectClosure)
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
    let y ← Code.termE t s
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
    | some (vr, cr) => pure (some (← need (.limit (.function r)) (Code.ite? r m vb vr), .ite m cb cr))
  | .guarded p g body rest, σ, s => do
    let (m, δ) ← encodePat L p s
    let (vg, cg) ← encode g (Codes.append δ σ)
    let (vb, cb) ← encode body (Codes.append δ σ)
    match ← encodeClauses rest σ s with
    | none => pure (some (vb, andT cg cb))
    | some (vr, cr) =>
      pure (some (← need (.limit (.function r)) (Code.ite? r (.and m vg) vb vr),
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
  if (L.find? t).isSome then L else { L with types := L.types ++ [(t, n)] }

section
variable (slots : Ty → Nat) (dsl : Layout → Dsl → List Ty → Layout)

mutual
/-- The layout with every datatype `t` needs: its fields' types first, so each datatype refers only to earlier
ones. A bag, table or list gets `slots` of its type, each a tuple of an occupied flag and the item. `dsl` adds what a
structure type needs. -/
def addTyWith (L : Layout) : Ty → Layout
  | .tuple ts => (addTysWith L ts).push (.tuple ts)
  | .adt 0 a vs => if (boolVs? vs).isSome then L else (addTyssWith L vs).push (.adt 0 a vs)
  | .adt (i + 1) a vs => (addTyssWith L vs).push (.adt (i + 1) a vs)
  | .id => L.push .id
  | .list t => ((addTyWith L t).push (.tuple [Ty.bool, t])).push (.list t) (slots (.list t))
  | .fn ps r => addTyWith (addTysWith L ps) r
  | .bag t => ((addTyWith L t).push (.tuple [Ty.bool, t])).push (.bag t) (slots (.bag t))
  | .table k v => (((addTyWith (addTyWith L k) v)).push (.tuple [Ty.bool, k, v])).push (.table k v) (slots (.table k v))
  | .dsl k a => dsl L k a
  | .int | .str | .date | .param _ => L
def addTysWith (L : Layout) : List Ty → Layout
  | [] => L
  | t :: ts => addTysWith (addTyWith L t) ts
def addTyssWith (L : Layout) : List (List Ty) → Layout
  | [] => L
  | ts :: vs => addTyssWith (addTysWith L ts) vs
end

/-- The effect datatype of the event type `e`, after the types of its kinds' fields, which are data. -/
def addEffect (L : Layout) (e : Ty) : Layout :=
  ((L.effectFields e).foldl (fun L fs => addTysWith slots (fun L _ _ => L) L fs) L).push (.dsl .effect [e])

/-- The slot count of each type, except that a list of effects of an event type no effect kind names has none: no
effect value of that type has a code, so every list of them that has one is empty. -/
def effectSlots (L : Layout) : Ty → Nat
  | .list (.dsl .effect [e]) => if (L.effectFields e).isEmpty then 0 else slots (.list (.dsl .effect [e]))
  | t => slots t

/-- The layout with every datatype the types `ts` need, an effect type's included. -/
def addTys (L : Layout) (ts : List Ty) : Layout :=
  addTysWith (effectSlots slots L) (fun L k a => match k, a with
    | .effect, [e] => addEffect (effectSlots slots L) L e | _, _ => L) L ts

end

/-- The layout with the effect datatype of each event type its effect kinds name, after the types of their fields. -/
def addEffects (slots : Ty → Nat) (L : Layout) : Layout :=
  (L.effects.map (·.event) ++ L.owns.map (·.event)).foldl (addEffect slots) L

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
  -- A datatype needs a constructor (SMT-LIB declares none without one), so a type without variants gets one that codes
  -- no value; so does the effect datatype with no kind.
  | (.adt _ _ [], _) => some ⟨[[]]⟩
  | (.adt _ _ vs, _) => do pure ⟨← vs.mapM (·.mapM L.srt?)⟩
  | (.id, _) => some ⟨[[.int, .int], [.str]]⟩
  | (.bag t, n) | (.list t, n) => do pure ⟨[List.replicate n (← L.srt? (.tuple [Ty.bool, t]))]⟩
  | (.table k v, n) => do pure ⟨[List.replicate n (← L.srt? (.tuple [Ty.bool, k, v]))]⟩
  | (.dsl .effect [e], _) => match L.effectFields e with
    | [] => some ⟨[[]]⟩
    | fss => do pure ⟨← fss.mapM (·.mapM L.srt?)⟩
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
  | .close _ env _ _ body | .closeEffect _ env _ _ body => t :: Exprs.tys env ++ Expr.tys body
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
  | .close _ env _ _ body | .closeEffect _ env _ _ body => Exprs.lits env ++ Expr.lits body
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
