import Tazuna.Semantics.Data
import Tazuna.Trace.Date

/-! How a data value crosses the wire, by its type. A trace holds JSON; `Wire` is that JSON with objects as lists of
pairs, so that reading a value back is a theorem about lists (`dec_enc`). Turning text into `Wire` and back is Lean's
JSON library.

- An Int is a number and a String a string.
- A List, a Bag and a tuple are arrays; a Bag's array is a multiset.
- A Table is an array of `[key, value]` pairs.
- A Bool is `true` or `false`, and Nil is `null`: JSON's own literals.
- A value of any other custom type, `Option` and `Result` included, is an object: `"tag"` names the variant, and each
  field sits under its label, or under its position (`"0"`, `"1"`) when it has none.
- A Date is its label `YYYY-MM-DD`.
- An Id is a string a binding names it by: a trace names ids by their first appearance, never by the engine's numbers.

Functions and fresh-id sources never cross the wire. -/

namespace Tazuna.Trace

open Tazuna.Ir

inductive Wire where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (xs : List Wire)
  | obj (kvs : List (String × Wire))
deriving Inhabited, Repr

instance {κ ν : Type} (f : κ → κ → Bool) (xs : List (κ × ν)) : Decidable (KeysUnique f xs) := by
  unfold KeysUnique; infer_instance

/-- The keys a variant's fields sit under: their labels, or their positions. -/
def fieldKeys (fs : List Field) : List String :=
  fs.zipIdx.map fun (f, k) => f.label.getD (toString k)

/-- Whether a variant can be written: its name finds it first among the variants, and its keys are distinct and none
is `tag`. -/
def writable (decl : List Variant) (k : Nat) (var : Variant) : Bool :=
  decl.findIdx? (·.name == var.name) == some k && (fieldKeys var.fields).Nodup && !(fieldKeys var.fields).contains "tag"

/-- A Bool: the prelude's type 0, whose variants `True` and `False` have no fields. -/
def encBool : (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → Option Wire
  | [] :: _, .inl _ => some (.bool true)
  | _ :: vs, .inr y => match vs, y with
    | [] :: _, .inl _ => some (.bool false)
    | _, _ => none
  | _, _ => none

/-- Nil: the prelude's type 1, whose one variant has no fields. -/
def encNil : (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → Option Wire
  | [] :: _, .inl _ => some .null
  | _, _ => none

def decBool : (vs : List (List Ty)) → Wire → Option (Ty.semAltsWith Dsl.base vs).1
  | [] :: _, .bool true => some (.inl ())
  | _ :: [] :: _, .bool false => some (.inr (.inl ()))
  | _, _ => none

def decNil : (vs : List (List Ty)) → Wire → Option (Ty.semAltsWith Dsl.base vs).1
  | [] :: _, .null => some (.inl ())
  | _, _ => none

section
variable (T : List TypeDecl) (name : Nat → Option String)

mutual
/-- The wire form of a value of type `t`, when it has one. `name` writes ids. -/
def enc : (t : Ty) → t.den0 → Option Wire
  | .int, n => some (.num n)
  | .str, s => some (.str s)
  | .list t, xs => (xs.mapM (enc t)).map .arr
  | .bag t, xs => (xs.mapM (enc t)).map .arr
  | .tuple ts, x => (encs ts x).map .arr
  | .adt i _ vs, x =>
    if i = 0 then encBool vs x else if i = 1 then encNil vs x
    else encAlts ((T[i]?.map (·.variants)).getD []) 0 vs x
  | .table k v, x => (x.1.mapM fun (a, b) => do pure (Wire.arr [← enc k a, ← enc v b])).map .arr
  | .date, d => (renderDate? d).map .str
  | .id, n => (name n).map .str
  | .fn .., _ | .param _, _ | .dsl .., _ => none
def encs : (ts : List Ty) → (Ty.semsWith Dsl.base ts).1 → Option (List Wire)
  | [], () => some []
  | t :: ts, (x, xs) => do pure ((← enc t x) :: (← encs ts xs))
/-- A value of the variants `vs`, which are the declaration's variants from index `k` on. -/
def encAlts (decl : List Variant) (k : Nat) : (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → Option Wire
  | [], x => nomatch x
  | fs :: _, .inl x => do
    let var ← decl[k]?
    let ws ← encs fs x
    if writable decl k var && (fieldKeys var.fields).length == ws.length then
      pure (.obj (("tag", .str var.name) :: (fieldKeys var.fields).zip ws))
    else none
  | _ :: vs, .inr y => encAlts decl (k + 1) vs y
end

end

mutual
/-- The ids a value holds, in the order its wire form writes them. -/
def idsOf : (t : Ty) → t.den0 → List Nat
  | .list t, xs | .bag t, xs => xs.flatMap (idsOf t)
  | .tuple ts, x => idsOfs ts x
  | .adt _ _ vs, x => idsOfAlts vs x
  | .table k v, x => x.1.flatMap fun (a, b) => idsOf k a ++ idsOf v b
  | .id, n => [n]
  | .int, _ | .str, _ | .date, _ | .fn .., _ | .param _, _ | .dsl .., _ => []
def idsOfs : (ts : List Ty) → (Ty.semsWith Dsl.base ts).1 → List Nat
  | [], () => []
  | t :: ts, (x, xs) => idsOf t x ++ idsOfs ts xs
def idsOfAlts : (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → List Nat
  | [], x => nomatch x
  | fs :: _, .inl x => idsOfs fs x
  | _ :: vs, .inr y => idsOfAlts vs y
end

section
variable (T : List TypeDecl) (lookup : String → Option Nat)

mutual
/-- The value of type `t` a wire form writes, when it writes one. `lookup` reads ids. -/
def dec : (t : Ty) → Wire → Option t.den0
  | .int, .num n => some n
  | .str, .str s => some s
  | .list t, .arr ws => ws.mapM (dec t)
  | .bag t, .arr ws => ws.mapM (dec t)
  | .tuple ts, .arr ws => decs ts ws
  | .adt i _ vs, w =>
    if i = 0 then decBool vs w else if i = 1 then decNil vs w
    else match w with
      | .obj kvs => do
        let decl := (T[i]?.map (·.variants)).getD []
        let .str tag ← kvs.lookup "tag" | none
        let k ← decl.findIdx? (·.name == tag)
        decAlts decl kvs k 0 vs
      | _ => none
  | .table k v, .arr ws => do
    let pairs ← ws.mapM fun
      | .arr [a, b] => do pure (← dec k a, ← dec v b)
      | _ => none
    if h : KeysUnique (Ty.semWith Dsl.base k).2 pairs then some ⟨pairs, h⟩ else none
  | .date, .str s => parseDate? s
  | .id, .str s => lookup s
  | _, _ => none
def decs : (ts : List Ty) → List Wire → Option (Ty.semsWith Dsl.base ts).1
  | [], [] => some ()
  | t :: ts, w :: ws => do pure (← dec t w, ← decs ts ws)
  | _, _ => none
/-- The fields of `fs` under `keys` in `kvs`. -/
def decFields (kvs : List (String × Wire)) : (fs : List Ty) → List String → Option (Ty.semsWith Dsl.base fs).1
  | [], [] => some ()
  | f :: fs, key :: keys => do pure (← dec f (← kvs.lookup key), ← decFields kvs fs keys)
  | _, _ => none
/-- Variant `k` of the variants `vs`, which are the declaration's variants from index `j` on. -/
def decAlts (decl : List Variant) (kvs : List (String × Wire)) (k : Nat) (j : Nat) :
    (vs : List (List Ty)) → Option (Ty.semAltsWith Dsl.base vs).1
  | [] => none
  | fs :: vs =>
    if k = j then do
      let var ← decl[j]?
      pure (.inl (← decFields kvs fs (fieldKeys var.fields)))
    else (decAlts decl kvs k (j + 1) vs).map .inr
end

end

end Tazuna.Trace
