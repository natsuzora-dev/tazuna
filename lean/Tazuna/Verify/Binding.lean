/-!
A binding of snapshot values to implementation values, and the set of bindings that verify carries while it compares.

- Each value comes with its domain (Bound): the entity whose key it is, `request` for a request id, or "" for any other
  string. A binding pairs values one to one, and since a value carries its domain, values of different domains never
  meet.
- Binding a string only adds a pair, so a binding keeps every pair that it held before (Binding.Extends).
- The set holds every binding that agrees with the lines compared so far, at most `bindingLimit` of them; a step that
  would hold more is reported, never cut silently.
-/

namespace Tazuna.Verify

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

end Tazuna.Verify
