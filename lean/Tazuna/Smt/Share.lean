import Tazuna.Smt.Term
import Std.Data.HashMap

/-! Sharing in scripts. The encoding marks with `Term.share` each value it may use more than once; as a tree such a
term repeats wherever it is used, so chained operations on one collection would grow the tree exponentially. A
script instead defines each distinct shared term once, `(define-fun s<i> () S body)`, and refers to it as `s<i>`
(hash-consing, as solvers keep terms internally). `Term.extract` finds repeats by the stored hash and confirms each
by equality, so a hash collision costs time, never meaning. `shared_agrees` proves that in every model of the
definitions the shared terms denote the tree's, and `shared_conservative` that every model of the tree's variables
extends to one of the definitions, so the shared script and the tree script are satisfiable together. -/

namespace Tazuna.Smt

/-- The definitions of a script's shared terms: entry `i` is `s<i>`, with the shared term and its body, the term
with each shared term inside it replaced by its reference. A body refers only to earlier definitions. -/
structure Defs where
  entries : Array (Term × Term) := #[]
  /-- Candidate entries by the shared term's hash. -/
  index : Std.HashMap UInt64 (List Nat) := {}

def Defs.find? (D : Defs) (h : UInt64) (t : Term) : Option Nat :=
  (D.index.getD h []).find? fun i => match D.entries[i]? with
    | some (o, _) => o.same t
    | none => false

def Defs.add (D : Defs) (h : UInt64) (t b : Term) : Defs :=
  { entries := D.entries.push (t, b), index := D.index.insert h (D.entries.size :: D.index.getD h []) }

mutual
/-- The term with each shared term replaced by a reference to its definition, and the definitions extended with the
shared terms seen for the first time, inner ones first. -/
def Term.extract : Term → Defs → Term × Defs
  | .shared h t, D => match D.find? h t with
    | some i => (.ref i, D)
    | none => let (b, D) := t.extract D; (.ref D.entries.size, D.add h t b)
  | .not a, D => let (a, D) := a.extract D; (.not a, D)
  | .len a, D => let (a, D) := a.extract D; (.len a, D)
  | .is d k a, D => let (a, D) := a.extract D; (.is d k a, D)
  | .sel d k j a, D => let (a, D) := a.extract D; (.sel d k j a, D)
  | .and a b, D => let (a, D) := a.extract D; let (b, D) := b.extract D; (.and a b, D)
  | .or a b, D => let (a, D) := a.extract D; let (b, D) := b.extract D; (.or a b, D)
  | .eq a b, D => let (a, D) := a.extract D; let (b, D) := b.extract D; (.eq a b, D)
  | .lt a b, D => let (a, D) := a.extract D; let (b, D) := b.extract D; (.lt a b, D)
  | .le a b, D => let (a, D) := a.extract D; let (b, D) := b.extract D; (.le a b, D)
  | .add a b, D => let (a, D) := a.extract D; let (b, D) := b.extract D; (.add a b, D)
  | .sub a b, D => let (a, D) := a.extract D; let (b, D) := b.extract D; (.sub a b, D)
  | .mul a b, D => let (a, D) := a.extract D; let (b, D) := b.extract D; (.mul a b, D)
  | .div a b, D => let (a, D) := a.extract D; let (b, D) := b.extract D; (.div a b, D)
  | .mod a b, D => let (a, D) := a.extract D; let (b, D) := b.extract D; (.mod a b, D)
  | .cat a b, D => let (a, D) := a.extract D; let (b, D) := b.extract D; (.cat a b, D)
  | .slt a b, D => let (a, D) := a.extract D; let (b, D) := b.extract D; (.slt a b, D)
  | .ite c a b, D =>
    let (c, D) := c.extract D; let (a, D) := a.extract D; let (b, D) := b.extract D; (.ite c a b, D)
  | .ctor d k args, D => let (args, D) := Term.extracts args D; (.ctor d k args, D)
  | t@(.var _), D | t@(.int _), D | t@(.str _), D | t@(.bool _), D | t@(.ref _), D => (t, D)
def Term.extracts : List Term → Defs → List Term × Defs
  | [], D => ([], D)
  | t :: ts, D => let (t, D) := t.extract D; let (ts, D) := Term.extracts ts D; (t :: ts, D)
end

/-! Correctness. -/

/-- `D'` keeps every entry of `D`. -/
def Defs.Le (D D' : Defs) : Prop := ∀ (i : Nat) (e : Term × Term), D.entries[i]? = some e → D'.entries[i]? = some e

/-- The model gives each definition its shared term's value. -/
def Defs.Agree (M : Model) (D : Defs) : Prop := ∀ i o b, D.entries[i]? = some (o, b) → M.defs i = o.denote M

/-- The model gives each definition its body's value: what `define-fun` means. -/
def Defs.Sat (M : Model) (D : Defs) : Prop := ∀ i o b, D.entries[i]? = some (o, b) → M.defs i = b.denote M

/-- Each body denotes its shared term wherever the earlier definitions have their shared terms' values. -/
def Defs.Wf (D : Defs) : Prop :=
  ∀ i o b, D.entries[i]? = some (o, b) → ∀ M : Model,
    (∀ j o' b', j < i → D.entries[j]? = some (o', b') → M.defs j = o'.denote M) → b.denote M = o.denote M

theorem Defs.le_refl (D : Defs) : D.Le D := fun _ _ h => h

theorem Defs.le_trans {A B C : Defs} (h1 : A.Le B) (h2 : B.Le C) : A.Le C := fun i e h => h2 i e (h1 i e h)

theorem Defs.agree_of_le {M : Model} {D D' : Defs} (hl : D.Le D') (h : D'.Agree M) : D.Agree M :=
  fun i o b he => h i o b (hl i _ he)

theorem Defs.le_add (D : Defs) (h : UInt64) (t b : Term) : D.Le (D.add h t b) := by
  intro i e he
  simp only [Defs.add, Array.getElem?_push]
  have : i < D.entries.size := (Array.getElem?_eq_some_iff.1 he).1
  simp [Nat.ne_of_lt this, he]

theorem Defs.find?_some {D : Defs} {h : UInt64} {t : Term} {i : Nat} (hf : D.find? h t = some i) :
    ∃ b, D.entries[i]? = some (t, b) := by
  simp only [Defs.find?] at hf
  have hp := List.find?_some hf
  revert hp
  split
  · rename_i o b he; intro hp; exact ⟨b, by rw [he, Term.eq_of_same hp]⟩
  · intro hp; cases hp

theorem Defs.wf_add {D : Defs} (hw : D.Wf) (h : UInt64) (t b : Term)
    (hb : ∀ M, D.Agree M → b.denote M = t.denote M) : (D.add h t b).Wf := by
  intro i o b' he M hj
  simp only [Defs.add, Array.getElem?_push] at he
  split at he
  · cases he; subst_vars
    refine hb M fun j o' b'' hj' => ?_
    have hlt : j < D.entries.size := (Array.getElem?_eq_some_iff.1 hj').1
    exact hj j o' b'' hlt (by simp [Defs.add, Array.getElem?_push, Nat.ne_of_lt hlt, hj'])
  · rename_i hne
    refine hw i o b' he M fun j o' b'' hji hj' => hj j o' b'' hji ?_
    have hlt : j < D.entries.size := (Array.getElem?_eq_some_iff.1 hj').1
    simp [Defs.add, Array.getElem?_push, Nat.ne_of_lt hlt, hj']

/-- What extraction keeps: well-formed definitions, the old entries, and the term's meaning wherever the definitions
agree with their shared terms. -/
def ExtractOk (t : Term) (D : Defs) (r : Term × Defs) : Prop :=
  r.2.Wf ∧ D.Le r.2 ∧ ∀ M, r.2.Agree M → r.1.denote M = t.denote M

def ExtractsOk (ts : List Term) (D : Defs) (r : List Term × Defs) : Prop :=
  r.2.Wf ∧ D.Le r.2 ∧ ∀ M, r.2.Agree M → Term.denotes M r.1 = Term.denotes M ts

theorem extract_one {a : Term} {D : Defs} {r : Term × Defs} (f : Term → Term) (g : Term)
    (hg : ∀ M, (∀ x, x.denote M = a.denote M → (f x).denote M = g.denote M)) (h : ExtractOk a D r) :
    ExtractOk g D (f r.1, r.2) :=
  ⟨h.1, h.2.1, fun M hM => hg M _ (h.2.2 M hM)⟩

theorem extract_two {a b : Term} {D : Defs} {r : Term × Defs} {r' : Term × Defs} (f : Term → Term → Term) (g : Term)
    (hg : ∀ M, (∀ x y, x.denote M = a.denote M → y.denote M = b.denote M → (f x y).denote M = g.denote M))
    (ha : ExtractOk a D r) (hb : ExtractOk b r.2 r') : ExtractOk g D (f r.1 r'.1, r'.2) :=
  ⟨hb.1, Defs.le_trans ha.2.1 hb.2.1, fun M hM =>
    hg M _ _ (ha.2.2 M (Defs.agree_of_le hb.2.1 hM)) (hb.2.2 M hM)⟩

mutual
theorem Term.extract_ok : (t : Term) → (D : Defs) → D.Wf → ExtractOk t D (t.extract D)
  | .shared h t, D, hw => by
    unfold Term.extract
    split
    · rename_i i hf
      obtain ⟨b, hb⟩ := Defs.find?_some hf
      exact ⟨hw, Defs.le_refl D, fun M hM => by simp [Term.denote, hM i t b hb]⟩
    · have ih := Term.extract_ok t D hw
      refine ⟨Defs.wf_add ih.1 h t _ ih.2.2, Defs.le_trans ih.2.1 (Defs.le_add _ h t _), fun M hM => ?_⟩
      have := hM (t.extract D).2.entries.size t (t.extract D).1 (by simp [Defs.add])
      simp [Term.denote, this]
  | .not a, D, hw => extract_one .not _ (fun M x hx => by simp [Term.denote, hx]) (Term.extract_ok a D hw)
  | .len a, D, hw => extract_one .len _ (fun M x hx => by simp [Term.denote, hx]) (Term.extract_ok a D hw)
  | .is d k a, D, hw => extract_one (.is d k) _ (fun M x hx => by simp [Term.denote, hx]) (Term.extract_ok a D hw)
  | .sel d k j a, D, hw =>
    extract_one (.sel d k j) _ (fun M x hx => by simp [Term.denote, hx]) (Term.extract_ok a D hw)
  | .and a b, D, hw | .or a b, D, hw | .eq a b, D, hw | .lt a b, D, hw | .le a b, D, hw | .add a b, D, hw
  | .sub a b, D, hw | .mul a b, D, hw | .div a b, D, hw | .mod a b, D, hw | .cat a b, D, hw
  | .slt a b, D, hw => by
    have ha := Term.extract_ok a D hw
    have hb := Term.extract_ok b _ ha.1
    exact extract_two _ _ (fun M x y hx hy => by simp [Term.denote, hx, hy]) ha hb
  | .ite c a b, D, hw => by
    have hc := Term.extract_ok c D hw
    have ha := Term.extract_ok a _ hc.1
    have hb := Term.extract_ok b _ ha.1
    refine ⟨hb.1, Defs.le_trans hc.2.1 (Defs.le_trans ha.2.1 hb.2.1), fun M hM => ?_⟩
    have ea := ha.2.2 M (Defs.agree_of_le hb.2.1 hM)
    have ec := hc.2.2 M (Defs.agree_of_le (Defs.le_trans ha.2.1 hb.2.1) hM)
    simp [Term.extract, Term.denote, ea, ec, hb.2.2 M hM]
  | .ctor d k args, D, hw => by
    have h := Term.extracts_ok args D hw
    exact ⟨h.1, h.2.1, fun M hM => by simp [Term.extract, Term.denote, h.2.2 M hM]⟩
  | .var _, D, hw | .int _, D, hw | .str _, D, hw | .bool _, D, hw | .ref _, D, hw =>
    ⟨hw, Defs.le_refl D, fun _ _ => rfl⟩
theorem Term.extracts_ok : (ts : List Term) → (D : Defs) → D.Wf → ExtractsOk ts D (Term.extracts ts D)
  | [], D, hw => ⟨hw, Defs.le_refl D, fun _ _ => rfl⟩
  | t :: ts, D, hw => by
    have ht := Term.extract_ok t D hw
    have hs := Term.extracts_ok ts _ ht.1
    refine ⟨hs.1, Defs.le_trans ht.2.1 hs.2.1, fun M hM => ?_⟩
    simp [Term.extracts, Term.denotes, ht.2.2 M (Defs.agree_of_le hs.2.1 hM), hs.2.2 M hM]
end

theorem Defs.wf_empty : ({} : Defs).Wf := by intro i o b h; simp at h

/-- In a model of well-formed definitions, each definition has its shared term's value. -/
theorem Defs.agree_of_sat {D : Defs} (hw : D.Wf) {M : Model} (hs : D.Sat M) : D.Agree M := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro o b he
    rw [hs i o b he]
    exact hw i o b he M fun j o' b' hj he' => ih j hj o' b' he'

/-- Sharing is sound: in every model of the definitions, the shared terms denote what the trees denote. -/
theorem shared_agrees (ts : List Term) (M : Model) (hs : (Term.extracts ts {}).2.Sat M) :
    Term.denotes M (Term.extracts ts {}).1 = Term.denotes M ts := by
  have h := Term.extracts_ok ts {} Defs.wf_empty
  exact h.2.2 M (Defs.agree_of_sat h.1 hs)

/-! Conservativity: the definitions constrain nothing else. -/

mutual
/-- Whether no definition is referred to: true of every term the encoding builds. -/
def Term.refFree : Term → Bool
  | .ref _ => false
  | .shared _ a | .not a | .len a | .is _ _ a | .sel _ _ _ a => a.refFree
  | .and a b | .or a b | .eq a b | .lt a b | .le a b | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .cat a b | .slt a b => a.refFree && b.refFree
  | .ite c a b => c.refFree && a.refFree && b.refFree
  | .ctor _ _ args => Term.refFrees args
  | .var _ | .int _ | .str _ | .bool _ => true
def Term.refFrees : List Term → Bool
  | [] => true
  | t :: ts => t.refFree && Term.refFrees ts
end

mutual
theorem Term.denote_defs (M : Model) (f : Nat → Val) : (t : Term) → t.refFree = true →
    t.denote { M with defs := f } = t.denote M
  | .ref _, h => by simp [Term.refFree] at h
  | .shared _ a, h | .not a, h | .len a, h | .is _ _ a, h => by
    simp only [Term.refFree] at h; simp [Term.denote, Term.denote_defs M f a h]
  | .sel _ _ _ a, h => by
    simp only [Term.refFree] at h; simp only [Term.denote, Term.denote_defs M f a h]
  | .and a b, h | .or a b, h | .eq a b, h | .lt a b, h | .le a b, h | .add a b, h | .sub a b, h | .mul a b, h
  | .div a b, h | .mod a b, h | .cat a b, h | .slt a b, h => by
    simp only [Term.refFree, Bool.and_eq_true] at h
    simp [Term.denote, Term.denote_defs M f a h.1, Term.denote_defs M f b h.2]
  | .ite c a b, h => by
    simp only [Term.refFree, Bool.and_eq_true] at h
    simp [Term.denote, Term.denote_defs M f c h.1.1, Term.denote_defs M f a h.1.2, Term.denote_defs M f b h.2]
  | .ctor _ _ args, h => by
    simp only [Term.refFree] at h; simp [Term.denote, Term.denotes_defs M f args h]
  | .var _, _ | .int _, _ | .str _, _ | .bool _, _ => rfl
theorem Term.denotes_defs (M : Model) (f : Nat → Val) : (ts : List Term) → Term.refFrees ts = true →
    Term.denotes { M with defs := f } ts = Term.denotes M ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Term.refFrees, Bool.and_eq_true] at h
    simp [Term.denotes, Term.denote_defs M f t h.1, Term.denotes_defs M f ts h.2]
end

/-- Every shared term defined is free of references. -/
def Defs.RefFree (D : Defs) : Prop :=
  ∀ (i : Nat) (o b : Term), D.entries[i]? = some (o, b) → o.refFree = true

mutual
theorem Term.extract_refFree : (t : Term) → (D : Defs) → t.refFree = true → D.RefFree → (t.extract D).2.RefFree
  | .shared h t, D, ht, hD => by
    simp only [Term.refFree] at ht
    unfold Term.extract
    split
    · exact hD
    · have ih := Term.extract_refFree t D ht hD
      show Defs.RefFree (Defs.add _ h t _)
      intro i o b he
      simp only [Defs.add, Array.getElem?_push] at he
      split at he
      · cases he; exact ht
      · exact ih i o b he
  | .not a, D, ht, hD | .len a, D, ht, hD | .is _ _ a, D, ht, hD | .sel _ _ _ a, D, ht, hD => by
    simp only [Term.refFree] at ht; exact Term.extract_refFree a D ht hD
  | .and a b, D, ht, hD | .or a b, D, ht, hD | .eq a b, D, ht, hD | .lt a b, D, ht, hD | .le a b, D, ht, hD
  | .add a b, D, ht, hD | .sub a b, D, ht, hD | .mul a b, D, ht, hD | .div a b, D, ht, hD
  | .mod a b, D, ht, hD | .cat a b, D, ht, hD | .slt a b, D, ht, hD => by
    simp only [Term.refFree, Bool.and_eq_true] at ht
    exact Term.extract_refFree b _ ht.2 (Term.extract_refFree a D ht.1 hD)
  | .ite c a b, D, ht, hD => by
    simp only [Term.refFree, Bool.and_eq_true] at ht
    exact Term.extract_refFree b _ ht.2 (Term.extract_refFree a _ ht.1.2 (Term.extract_refFree c D ht.1.1 hD))
  | .ctor _ _ args, D, ht, hD => by
    simp only [Term.refFree] at ht; exact Term.extracts_refFree args D ht hD
  | .var _, _, _, hD | .int _, _, _, hD | .str _, _, _, hD | .bool _, _, _, hD => hD
  | .ref _, _, ht, _ => by simp [Term.refFree] at ht
theorem Term.extracts_refFree : (ts : List Term) → (D : Defs) → Term.refFrees ts = true → D.RefFree →
    (Term.extracts ts D).2.RefFree
  | [], _, _, hD => hD
  | t :: ts, D, ht, hD => by
    simp only [Term.refFrees, Bool.and_eq_true] at ht
    exact Term.extracts_refFree ts _ ht.2 (Term.extract_refFree t D ht.1 hD)
end

/-- Sharing is conservative: every model, whatever it gives the definitions, has a variant that differs only in
the definitions and satisfies them. So a shared script is unsat exactly when the tree script is. -/
theorem shared_conservative (ts : List Term) (hr : Term.refFrees ts = true) (M : Model) :
    ∃ f, (Term.extracts ts {}).2.Sat { M with defs := f } := by
  let D := (Term.extracts ts {}).2
  have hD : D.RefFree := Term.extracts_refFree ts {} hr (fun i o b h => by simp at h)
  let f : Nat → Val := fun i => match D.entries[i]? with
    | some (o, _) => o.denote M
    | none => M.defs i
  have hag : D.Agree { M with defs := f } := by
    intro i o b he
    simp only [f, he]
    exact (Term.denote_defs M f o (hD i o b he)).symm
  refine ⟨f, fun i o b he => ?_⟩
  have hw := (Term.extracts_ok ts {} Defs.wf_empty).1
  rw [hag i o b he]
  exact (hw i o b he _ fun j o' b' _ he' => hag j o' b' he').symm

end Tazuna.Smt
