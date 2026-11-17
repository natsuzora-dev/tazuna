import Lean.Data.Json.Printer
import Tazuna.Data.Collections
import Tazuna.Data.List
import Tazuna.Data.Names

/-!
This module defines the values that verify and the peer check compare. TS reads a line by its definition's schema,
re-encodes it, and wraps bags, sets and sortedBy arrays. This module fixes how wrapped values compare.
-/

namespace Tazuna.Data

theorem sizeOf_snd_lt {α β : Type} [SizeOf α] [SizeOf β] {p : α × β} {l : List (α × β)} (h : p ∈ l) :
    sizeOf p.2 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h
  cases p; simp only [Prod.mk.sizeOf_spec, gt_iff_lt] at this ⊢; omega

/-- Proves that recursion into nested values terminates. -/
macro "nested_decreasing" : tactic =>
  `(tactic| (simp_wf; first
    | omega
    | (have := List.sizeOf_lt_of_mem (by assumption); omega)
    | (have := sizeOf_snd_lt (by assumption); omega)))

/-- Proves that a recursion whose measure is a lexicographic pair decreases. -/
macro "lex_decreasing" : tactic =>
  `(tactic| (simp_wf; simp only [Prod.lex_def] at *; first | done | omega | (simp_all; done) | (simp_all; omega)))

/--
A value as verify compares it. `bag` is an array compared without element order. `runs` is a sortedBy array as runs
of elements with equal keys, each a bag. `leaf` is null, a boolean, a number or a string.
-/
inductive CValue where
  | leaf (v : Value)
  | arr (elements : List CValue)
  | obj (fields : List (String × CValue))
  | bag (elements : List CValue)
  | runs (runs : List CValue)
deriving Repr, Inhabited

/-- Whether two field lists have the same keys. -/
def sameKeys (fs gs : List (String × CValue)) : Bool :=
  let ks := fs.map (·.1)
  let kt := gs.map (·.1)
  ks.length == kt.length && ks.all kt.contains && kt.all ks.contains

/-- The CValue of a value that no schema reads. -/
def CValue.ofValue : Value → CValue
  | .arr vs => .arr (vs.map CValue.ofValue)
  | .obj fs => .obj (fs.map fun p => (p.1, CValue.ofValue p.2))
  | v => .leaf v
decreasing_by all_goals nested_decreasing

mutual

/-- The value that TS `JSON.stringify` writes: bag and runs become arrays of their elements. -/
def CValue.flatten : CValue → Value
  | .leaf v => v
  | .arr xs => .arr (CValue.flattenList xs)
  | .obj fs => .obj (CValue.flattenFields fs)
  | .bag xs => .arr (CValue.flattenList xs)
  | .runs rs => .arr (CValue.flattenRuns rs)

def CValue.flattenList : List CValue → List Value
  | [] => []
  | x :: xs => x.flatten :: CValue.flattenList xs

def CValue.flattenFields : List (String × CValue) → List (String × Value)
  | [] => []
  | (k, v) :: fs => (k, v.flatten) :: CValue.flattenFields fs

def CValue.flattenRuns : List CValue → List Value
  | [] => []
  | .bag xs :: rs => CValue.flattenList xs ++ CValue.flattenRuns rs
  | r :: rs => r.flatten :: CValue.flattenRuns rs

end

def sortStrings (xs : List String) : List String := xs.mergeSort fun a b => decide (a ≤ b)

mutual

/--
The text by which values compare, as TS `canonicalJson(orderFree(v))` writes it: elements of a bag, and of each run,
are sorted by text. Two texts are equal exactly when the values differ only in field order and bag element order.
-/
def CValue.key : CValue → String
  | .leaf v => v.canonical
  | .arr xs => arrayText (CValue.keyList xs)
  | .obj fs => objectText (CValue.keyFields fs)
  | .bag xs => arrayText (sortStrings (CValue.keyList xs))
  | .runs rs => arrayText (CValue.runKeys rs)

def CValue.keyList : List CValue → List String
  | [] => []
  | x :: xs => x.key :: CValue.keyList xs

def CValue.keyFields : List (String × CValue) → List (String × String)
  | [] => []
  | (k, v) :: fs => (k, v.key) :: CValue.keyFields fs

def CValue.runKeys : List CValue → List String
  | [] => []
  | .bag xs :: rs => sortStrings (CValue.keyList xs) ++ CValue.runKeys rs
  | r :: rs => r.key :: CValue.runKeys rs

end

mutual

def CValue.mapStrings (f : String → String) : CValue → CValue
  | .leaf (.str s) => .leaf (.str (f s))
  | .leaf v => .leaf v
  | .arr xs => .arr (CValue.mapStringsList f xs)
  | .obj fs => .obj (CValue.mapStringsFields f fs)
  | .bag xs => .bag (CValue.mapStringsList f xs)
  | .runs rs => .runs (CValue.mapStringsList f rs)

def CValue.mapStringsList (f : String → String) : List CValue → List CValue
  | [] => []
  | x :: xs => x.mapStrings f :: CValue.mapStringsList f xs

def CValue.mapStringsFields (f : String → String) : List (String × CValue) → List (String × CValue)
  | [] => []
  | (k, v) :: fs => (k, v.mapStrings f) :: CValue.mapStringsFields f fs

end

/-- Whether the value is a JS array or plain object. Bag and Runs are not plain. -/
def CValue.isPlain : CValue → Bool
  | .arr _ | .obj _ => true
  | _ => false

/-- Whether JS `typeof v === "object" && v !== null` holds. -/
def CValue.isObject : CValue → Bool
  | .leaf _ => false
  | _ => true

/-- The JS `Object.keys` of the value, with array indices as strings. -/
def CValue.keys : CValue → List String
  | .arr xs => (List.range xs.length).map toString
  | .obj fs => fs.map (·.1)
  | _ => []

/-- The JS `v[k]`, with arrays indexed by strings. -/
def CValue.at? : CValue → String → Option CValue
  | .arr xs, k => k.toNat?.bind (xs[·]?)
  | .obj fs, k => (fs.find? (·.1 == k)).map (·.2)
  | _, _ => none

/-- The keys of `s`, then the keys only in `t` (JS `new Set([...Object.keys(s), ...Object.keys(t)])`). -/
def unionKeys (s t : CValue) : List String :=
  s.keys ++ (t.keys.filter fun k => !s.keys.contains k)

theorem at?_sizeOf {c v : CValue} {k : String} (h : c.at? k = some v) : sizeOf v < sizeOf c := by
  cases c with
  | arr xs =>
    simp only [CValue.at?] at h
    cases hk : k.toNat? with
    | none => simp [hk] at h
    | some n =>
      simp only [hk, Option.bind_some] at h
      have hm := List.mem_of_getElem? h
      have := List.sizeOf_lt_of_mem hm
      simp only [CValue.arr.sizeOf_spec, gt_iff_lt]; omega
  | obj fs =>
    simp only [CValue.at?, Option.map_eq_some_iff] at h
    obtain ⟨⟨k', v'⟩, hf, rfl⟩ := h
    have hm := List.mem_of_find?_eq_some hf
    have := List.sizeOf_lt_of_mem hm
    simp only [Prod.mk.sizeOf_spec, CValue.obj.sizeOf_spec, gt_iff_lt] at this ⊢; omega
  | leaf _ | bag _ | runs _ => simp [CValue.at?] at h

/--
Whether `s` equals `t` as TS `plainEqual(s, t)` decides. Plain values compare key by key. Other values
compare by equality for leaves, or by canonicalJson when both are objects. `none` is undefined.
-/
def plainEqual (s t : Option CValue) : Bool :=
  match s, t with
  | none, none => true
  | some s, some t =>
    if s.isPlain && t.isPlain then
      (unionKeys s t).attach.all fun ⟨k, _⟩ =>
        match hs : s.at? k with
        | some sv =>
          have := at?_sizeOf hs
          plainEqual (some sv) (t.at? k)
        | none => (t.at? k).isNone
    else
      match s, t with
      | .leaf a, .leaf b => a == b
      | a, b => a.isObject && b.isObject && a.flatten.canonical == b.flatten.canonical
  | _, _ => false
termination_by (s.map sizeOf).getD 0
decreasing_by simp_wf; omega

end Tazuna.Data
