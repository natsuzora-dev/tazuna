import Tazuna.Semantics.Value.Canonical
import Tazuna.Ir.Trace

/-!
A binding of one side's values to another's, and the matching of two values under the set of bindings that agree with
them. Verify matches a snapshot with an implementation trace, and Explore matches two runs of a spec, whose created keys
differ only by a renaming.

- Each value comes with its domain (Bound): the entity whose key it is, `request` for a request id, or "" for any other
  string. A binding pairs values one to one, and since a value carries its domain, values of different domains never
  meet.
- Binding a string only adds a pair, so a binding keeps every pair that it held before (Binding.Extends).
- The set holds every binding that agrees with the values matched so far, at most `bindingLimit` of them; a step that
  would hold more is reported, never cut silently.
-/

namespace Tazuna.Semantics

open Tazuna.Ir

/-- A value with its domain: the domain first, then the value. -/
abbrev Bound := String × String

/-- Snapshot values paired with implementation values, one to one. -/
structure Binding where
  pairs : List (Bound × Bound)
  valid : (pairs.map Prod.fst).Nodup ∧ (pairs.map Prod.snd).Nodup

/-- `b'` keeps every pair of `b`. -/
def Binding.Extends (b b' : Binding) : Prop := ∀ p ∈ b.pairs, p ∈ b'.pairs

theorem Binding.Extends.refl (b : Binding) : b.Extends b := fun _ h => h

theorem Binding.Extends.trans {a b c : Binding} (hab : a.Extends b) (hbc : b.Extends c) : a.Extends c :=
  fun p h => hbc p (hab p h)

def Binding.empty : Binding := ⟨[], by simp⟩

/-- Whether two bindings hold the same pairs. -/
def Binding.same (a b : Binding) : Bool :=
  a.pairs.length == b.pairs.length && a.pairs.all b.pairs.contains

/-- The pairs of strings of the binding. -/
def Binding.strings (b : Binding) : Bindings := b.pairs.map fun (s, t) => (s.2, t.2)

/-- The implementation value that `b` binds snapshot value `s` to, or `s` itself when `b` binds it to none. -/
def Binding.image (b : Binding) (s : Bound) : String :=
  ((b.pairs.lookup s).map (·.2)).getD s.2

/-- The most bindings, or states of a group, that one step of a comparison holds. -/
def bindingLimit : Nat := 256

theorem nodup_append_single {α : Type} {l : List α} {x : α} (h : l.Nodup) (hx : x ∉ l) : (l ++ [x]).Nodup :=
  List.nodup_append.mpr ⟨h, by simp, fun a ha b hb e => by simp at hb; subst hb; subst e; exact hx ha⟩

/--
The binding with snapshot value `s` standing for implementation value `t` of the same domain. A bound `s` must stand
for `t`. Any other `s` binds when it is `fresh` or equals `t`, unless `t` already stands for a value of the domain; a
value of domain "" that equals `t` and is not fresh compares equal without entering the binding, so it never keeps a
fresh value from binding.
-/
def Binding.bindString (fresh : Bool) (b : Binding) (s t : Bound) : Option { b' : Binding // b.Extends b' } :=
  if hs : s ∈ b.pairs.map Prod.fst then
    if (s, t) ∈ b.pairs then some ⟨b, .refl b⟩ else none
  else if !fresh && s == t && s.1 == "" then some ⟨b, .refl b⟩
  else if ht : t ∈ b.pairs.map Prod.snd then none
  else if fresh || s == t then
    some ⟨⟨b.pairs ++ [(s, t)], by simpa using nodup_append_single b.valid.1 hs,
      by simpa using nodup_append_single b.valid.2 ht⟩, fun _ h => List.mem_append_left _ h⟩
  else none

theorem eq_of_map_nodup {α β : Type} {f : α → β} : ∀ {l : List α}, (l.map f).Nodup → ∀ {p q : α}, p ∈ l → q ∈ l →
    f p = f q → p = q
  | [], _, _, _, hp, _, _ => by simp at hp
  | a :: l, h, p, q, hp, hq, e => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    simp only [List.mem_cons] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · rfl
    · exact absurd e.symm (h.1 q hq)
    · exact absurd e (h.1 p hp)
    · exact eq_of_map_nodup h.2 hp hq e

/-- No value of the pairs is bound to two values, and no two values to one. -/
def OneToOne {α : Type} (bs : List (α × α)) : Prop := ∀ p ∈ bs, ∀ q ∈ bs, (p.1 = q.1 ↔ p.2 = q.2)

theorem Binding.pairs_oneToOne (b : Binding) : OneToOne b.pairs := by
  intro p hp q hq
  constructor
  · intro e; rw [eq_of_map_nodup b.valid.1 hp hq e]
  · intro e; rw [eq_of_map_nodup b.valid.2 hp hq e]

/--
The states, each once by `same` in the order of their first appearance, or `none` when they are more than
`bindingLimit`.
-/
def limited {σ : Type} (same : σ → σ → Bool) (states : List σ) : Option (List σ) :=
  let kept := states.foldl (fun acc s => if acc.any (same s) then acc else acc ++ [s]) []
  if kept.length > bindingLimit then none else some kept

/-- The successors of all the states, kept by `limited`; `none` when a state's successors or all of them are too many. -/
def expand {σ τ : Type} (same : τ → τ → Bool) (states : List σ) (next : σ → Option (List τ)) : Option (List τ) := do
  let all ← states.mapM next
  limited same all.flatten

/-- A binding that keeps every pair of `root`. -/
abbrev From (root : Binding) := { b : Binding // root.Extends b }

def From.same {root : Binding} (a b : From root) : Bool := a.val.same b.val

/--
The bindings under which a snapshot value or line compares equal with an implementation one, each extending `b`:
none when they differ, and `none` (no list) when they are more than `bindingLimit`.
-/
abbrev Matches (b : Binding) := Option (List (From b))

def Matches.one {b : Binding} : Option (From b) → Matches b
  | some c => some [c]
  | none => some []

def lift {root b : Binding} (h : root.Extends b) (cs : List (From b)) : List (From root) :=
  cs.map fun c => ⟨c.val, h.trans c.property⟩

def Matches.andThen {b : Binding} (m : Matches b) (f : (c : Binding) → Matches c) : Matches b := do
  expand From.same (← m) fun c => (f c.val).map (lift c.property)

/-- Whether two lists hold the same items, as sets. -/
def sameSet {α : Type} [BEq α] (a b : List α) : Bool := a.length == b.length && a.all b.contains

/--
What the comparison knows of the snapshot's values: the domain of each (valueDomains), the fresh ones so far, and
which values `image s t` lets a fresh `s` stand for. Verify lets it stand for any string, since the implementation
chooses its values in its own way; Explore compares two runs of the spec and lets a created key stand only for a key
that the other run created in the same domain.
-/
structure Values where
  domain : String → String
  fresh : List String
  image : String → String → Bool

/-- Whether snapshot value `s` may bind to `t` as a new value: `s` is fresh and may stand for `t`. -/
def Values.binds (v : Values) (s t : String) : Bool := v.fresh.contains s && v.image s t

/-- The binding with snapshot string `s` standing for implementation string `t`, both in the domain of `s`. -/
def Values.bind (v : Values) (b : Binding) (s t : String) : Matches b :=
  .one (b.bindString (v.binds s t) (v.domain s, s) (v.domain s, t))

mutual

/--
The bindings under which snapshot value `s` compares equal with implementation value `t`, extending `b`. A key
reference binds; any other string compares literally, whatever its form.
-/
def matchValue (v : Values) (b : Binding) : CValue → CValue → Matches b
  | .ref _ s, .ref _ t => v.bind b s t
  | .leaf x, .leaf y => some (if x == y then [⟨b, .refl b⟩] else [])
  | .arr xs, .arr ys | .runs xs, .runs ys => matchList v b xs ys
  | .obj fs, .obj gs => if sameKeys fs gs then matchFields v b fs gs else some []
  | .bag xs, .bag ys => if xs.length == ys.length then matchBag v b xs ys else some []
  | _, _ => some []
termination_by s _ => sizeOf s

def matchList (v : Values) (b : Binding) : List CValue → List CValue → Matches b
  | [], [] => some [⟨b, .refl b⟩]
  | x :: xs, y :: ys => (matchValue v b x y).andThen fun c => matchList v c xs ys
  | _, _ => some []
termination_by xs _ => sizeOf xs

def matchFields (v : Values) (b : Binding) :
    List (String × CValue) → List (String × CValue) → Matches b
  | [], _ => some [⟨b, .refl b⟩]
  | (k, x) :: fs, gs =>
    match gs.lookup k with
    | some y => (matchValue v b x y).andThen fun c => matchFields v c fs gs
    | none => some []
termination_by fs _ => sizeOf fs

/-- Each element of `xs`, in order, pairs with each unpaired element of `ys` that it compares equal with. -/
def matchBag (v : Values) (b : Binding) (xs ys : List CValue) : Matches b := do
  let same (p q : From b × List Nat) : Bool := p.1.same q.1 && sameSet p.2 q.2
  let step (states : List (From b × List Nat)) (x : { x // x ∈ xs }) : Option (List (From b × List Nat)) :=
    expand same states fun (c, used) => do
      let next ← ((ys.zipIdx.filter fun (_, j) => !used.contains j).mapM fun (y, j) =>
        (matchValue v c.val x.1 y).map fun ds => (lift c.property ds).map ((·, used ++ [j])))
      pure next.flatten
  let paired ← xs.attach.foldlM step [(⟨b, .refl b⟩, [])]
  limited From.same (paired.map (·.1))
termination_by sizeOf xs
decreasing_by exact List.sizeOf_lt_of_mem x.2

end

/--
How two values compare up to a renaming: equal under some binding, under none, or not known because the bindings to
try exceed bindingLimit.
-/
inductive Sameness where
  | same
  | different
  | uncomparable
deriving DecidableEq, Repr

def Sameness.of (b : Bool) : Sameness := if b then .same else .different

def Matches.sameness {b : Binding} : Matches b → Sameness
  | some (_ :: _) => .same
  | some [] => .different
  | none => .uncomparable

/-- Same when one comparison is same, else uncomparable when one is, else different. -/
def Sameness.any (all : List Sameness) : Sameness :=
  if all.contains .same then .same else if all.contains .uncomparable then .uncomparable else .different

def matchOption (v : Values) (b : Binding) : Option CValue → Option CValue → Matches b
  | none, none => some [⟨b, .refl b⟩]
  | some s, some t => matchValue v b s t
  | _, _ => some []

end Tazuna.Semantics
