import Tazuna.Verify.Compare

namespace Tazuna.Thm.Verify.Compare

open Tazuna.Data Tazuna.Verify

def SelfBound (m : Bindings) : Prop := ∀ k vs, m.lookup k = some vs → k ∈ vs

theorem lookup_setAt {β : Type} (m : List (String × β)) (k k' : String) (v : β) :
    (setAt m k v).lookup k' = if k' = k then some v else m.lookup k' := by
  induction m with
  | nil => by_cases h : k' = k <;> simp [setAt, List.lookup, h, beq_eq_false_iff_ne.mpr]
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    by_cases ha : a = k
    · subst ha; by_cases h : k' = a <;> simp [setAt, List.lookup, h, beq_eq_false_iff_ne.mpr]
    · have : (a == k) = false := by simpa using ha
      simp only [setAt, this]
      by_cases h : k' = k
      · subst h
        simp [List.lookup, ih, beq_eq_false_iff_ne.mpr (Ne.symm ha)]
      · by_cases h2 : k' = a
        · subst h2; simp [List.lookup, h]
        · simp [List.lookup, ih, h, beq_eq_false_iff_ne.mpr h2]

theorem SelfBound.set {m : Bindings} (h : SelfBound m) (k : String) (vs : List String) (hk : k ∈ vs) :
    SelfBound (setAt m k vs) := by
  intro k' vs' hl
  rw [lookup_setAt] at hl
  by_cases e : k' = k
  · subst e; simp only [↓reduceIte, Option.some.injEq] at hl; subst hl; exact hk
  · simp only [e, ↓reduceIte] at hl; exact h k' vs' hl

theorem foldl_preserve {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (init : β), (∀ b a, a ∈ l → P b → P (f b a)) → P init → P (l.foldl f init)
  | [], _, _, h => h
  | a :: as, init, hf, h => foldl_preserve P f as (f init a) (fun b x hx => hf b x (List.mem_cons_of_mem a hx))
      (hf init a List.mem_cons_self h)

theorem bindValues_self (d : List String) (s : CValue) (m : Bindings) (h : SelfBound m) :
    SelfBound (bindValues d (some s) (some s) m) := by
  by_cases hstr : ∃ v, s = .leaf (.str v)
  · obtain ⟨v, rfl⟩ := hstr
    rw [bindValues]
    split
    · split
      · exact h
      · exact h.set v [v] List.mem_cons_self
    · exact h
  · rw [bindValues]
    · split
      · apply foldl_preserve _ _ _ _ _ h
        rintro b ⟨k, hk⟩ _ hb
        dsimp only
        split
        · rename_i sv hs
          have := at?_sizeOf hs
          rw [hs]
          exact bindValues_self d sv b hb
        · exact hb
      · exact h
    · intro v e; exact hstr ⟨v, e⟩
termination_by sizeOf s

mutual
def Distinct : CValue → Prop
  | .leaf _ => True
  | .arr xs | .bag xs | .runs xs => DistinctList xs
  | .obj fs => (fs.map (·.1)).Nodup ∧ DistinctFields fs
def DistinctList : List CValue → Prop
  | [] => True
  | x :: xs => Distinct x ∧ DistinctList xs
def DistinctFields : List (String × CValue) → Prop
  | [] => True
  | (_, v) :: fs => Distinct v ∧ DistinctFields fs
end

theorem lookup_of_mem {β : Type} : ∀ {fs : List (String × β)} {k : String} {v : β},
    (fs.map (·.1)).Nodup → (k, v) ∈ fs → fs.lookup k = some v
  | [], _, _, _, h => absurd h List.not_mem_nil
  | (a, b) :: fs, k, v, hn, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    rcases List.mem_cons.mp h with e | e
    · cases e; simp [List.lookup]
    · have hka : k ≠ a := fun hk => hn.1 (k, v) e hk
      simp [List.lookup, beq_eq_false_iff_ne.mpr hka, lookup_of_mem hn.2 e]

theorem all_contains_self (xs : List String) : xs.all xs.contains = true := by
  simp [List.all_eq_true]

mutual

theorem equal_refl (d : List String) (s : CValue) (m : Bindings) (inInputLine : Bool) (hd : Distinct s)
    (h : SelfBound m) : (equal d s s m inInputLine).1 = true ∧ SelfBound (equal d s s m inInputLine).2 := by
  match s with
  | .leaf (.str v) =>
    rw [equal]
    split
    · rename_i same hl
      simp [h v same hl, h]
    · simp [h]
  | .leaf .null | .leaf (.bool _) | .leaf (.num _) | .leaf (.arr _) | .leaf (.obj _) =>
    rw [equal] <;> simp [h]
  | .runs rs =>
    rw [equal]; simp only [beq_self_eq_true, ite_true]
    exact equalList_refl d rs m inInputLine hd h
  | .arr xs =>
    rw [equal]; simp only [beq_self_eq_true, ite_true]
    exact equalList_refl d xs m inInputLine hd h
  | .bag xs =>
    rw [equal]
    obtain ⟨m', hm, hb⟩ := matchBag_refl d xs m inInputLine hd h
    simp [hm, hb]
  | .obj fs =>
    rw [equal]
    simp only [Distinct] at hd
    simp only [beq_self_eq_true, all_contains_self, Bool.and_self, ite_true]
    exact equalFields_refl d fs fs m inInputLine hd.2 (fun k v hm => lookup_of_mem hd.1 hm) h
termination_by sizeOf s

theorem equalList_refl (d : List String) (xs : List CValue) (m : Bindings) (inInputLine : Bool)
    (hd : DistinctList xs) (h : SelfBound m) :
    (equalList d xs xs m inInputLine).1 = true ∧ SelfBound (equalList d xs xs m inInputLine).2 := by
  match xs with
  | [] => rw [equalList]; exact ⟨rfl, h⟩
  | x :: xs =>
    rw [equalList]
    simp only [DistinctList] at hd
    obtain ⟨he, hm⟩ := equal_refl d x m inInputLine hd.1 h
    split
    · rename_i m' e
      rw [e] at hm
      exact equalList_refl d xs m' inInputLine hd.2 hm
    · rename_i m' e
      rw [e] at he; cases he
termination_by sizeOf xs

theorem equalFields_refl (d : List String) (fs gs : List (String × CValue)) (m : Bindings) (inInputLine : Bool)
    (hd : DistinctFields fs) (hg : ∀ k v, (k, v) ∈ fs → gs.lookup k = some v) (h : SelfBound m) :
    (equalFields d fs gs m inInputLine).1 = true ∧ SelfBound (equalFields d fs gs m inInputLine).2 := by
  match fs with
  | [] => rw [equalFields]; exact ⟨rfl, h⟩
  | (k, v) :: fs =>
    rw [equalFields]
    simp only [DistinctFields] at hd
    rw [hg k v List.mem_cons_self]
    obtain ⟨he, hm⟩ := equal_refl d v m inInputLine hd.1 h
    simp only
    split
    · rename_i m' e
      rw [e] at hm
      exact equalFields_refl d fs gs m' inInputLine hd.2 (fun k v hm => hg k v (List.mem_cons_of_mem _ hm)) hm
    · rename_i m' e
      rw [e] at he; cases he
termination_by sizeOf fs

theorem matchBag_refl (d : List String) (xs : List CValue) (m : Bindings) (inInputLine : Bool)
    (hd : DistinctList xs) (h : SelfBound m) :
    ∃ m', matchBag d xs xs m inInputLine = some m' ∧ SelfBound m' := by
  match xs with
  | [] => rw [matchBag]; exact ⟨m, by simp, h⟩
  | x :: xs =>
    rw [matchBag]
    simp only [DistinctList] at hd
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
    rw [matchBagFrom]
    simp only [List.contains_nil, Bool.false_eq_true, ite_false, List.reverse_nil, List.nil_append]
    obtain ⟨he, hm⟩ := equal_refl d x (bindValues d (some x) (some x) m) inInputLine hd.1 (bindValues_self d x m h)
    split
    · rename_i m' e
      rw [e] at hm
      obtain ⟨r, hr, hb⟩ := matchBag_refl d xs m' inInputLine hd.2 hm
      exact ⟨r, by simp [hr], hb⟩
    · rename_i m' e
      rw [e] at he; cases he
termination_by sizeOf xs

end

def FlattenInjective (ys : List CValue) : Prop := ∀ a ∈ ys, ∀ b ∈ ys, a.flatten = b.flatten → a = b

theorem FlattenInjective.sub {ys zs : List CValue} (h : FlattenInjective ys) (hs : ∀ a ∈ zs, a ∈ ys) :
    FlattenInjective zs := fun a ha b hb e => h a (hs a ha) b (hs b hb) e

theorem matchBagFrom_scan (d : List String) (first : CValue) (rest : List CValue) (inInputLine : Bool)
    (hfirst : Distinct first)
    (IH : ∀ zs m', rest.Perm zs → FlattenInjective zs → SelfBound m' → (matchBag d rest zs m' inInputLine).isSome) :
    ∀ (cands passed : List CValue) (tried : List Value) (m : Bindings),
      first ∈ cands → (∀ v ∈ tried, v ≠ first.flatten) →
      (first :: rest).Perm (passed.reverse ++ cands) → FlattenInjective (passed ++ cands) → SelfBound m →
      (matchBagFrom d first rest cands passed tried m inInputLine).isSome
  | [], _, _, _, hmem, _, _, _, _ => absurd hmem List.not_mem_nil
  | t :: more, passed, tried, m, hmem, htried, hperm, hinj, h => by
    rw [matchBagFrom]
    by_cases ht : t = first
    · subst ht
      have hnt : tried.contains t.flatten = false := by
        simp only [List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq]
        intro v hv e; exact htried v hv e.symm
      simp only [hnt, Bool.false_eq_true, ite_false]
      obtain ⟨he, hm⟩ := equal_refl d t (bindValues d (some t) (some t) m) inInputLine hfirst (bindValues_self d t m h)
      split
      · rename_i m' e
        rw [e] at hm
        have hp : rest.Perm (passed.reverse ++ more) :=
          List.Perm.cons_inv (hperm.trans List.perm_middle)
        have hi : FlattenInjective (passed.reverse ++ more) :=
          hinj.sub (by intro a ha; simp only [List.mem_append, List.mem_reverse, List.mem_cons] at ha ⊢; grind)
        have := IH _ m' hp hi hm
        split
        · rfl
        · rename_i e2; rw [e2] at this; cases this
      · rename_i m' e
        rw [e] at he; cases he
    · have hmore : first ∈ more := by
        rcases List.mem_cons.mp hmem with e | e
        · exact absurd e.symm ht
        · exact e
      have hperm' : (first :: rest).Perm ((t :: passed).reverse ++ more) := by simpa using hperm
      have hinj' : FlattenInjective ((t :: passed) ++ more) :=
        hinj.sub (by intro a ha; simp only [List.mem_append, List.mem_cons] at ha ⊢; grind)
      split
      · exact matchBagFrom_scan d first rest inInputLine hfirst IH more (t :: passed) tried m hmore htried hperm' hinj' h
      · have htried' : ∀ v ∈ t.flatten :: tried, v ≠ first.flatten := by
          intro v hv
          rcases List.mem_cons.mp hv with e | e
          · subst e; intro hf
            exact ht (hinj t (by simp) first (by simp [hmem]) hf)
          · exact htried v e
        have next := matchBagFrom_scan d first rest inInputLine hfirst IH more (t :: passed) (t.flatten :: tried) m hmore
          htried' hperm' hinj' h
        dsimp only
        split
        · split
          · rfl
          · exact next
        · exact next

/-- The theorem assumes FlattenInjective because matchBag tries only one of several candidates with the same JSON. -/
theorem matchBag_perm (d : List String) (inInputLine : Bool) :
    ∀ (xs ys : List CValue) (m : Bindings), DistinctList xs → xs.Perm ys → FlattenInjective ys →
      SelfBound m → (matchBag d xs ys m inInputLine).isSome
  | [], ys, m, _, hp, _, _ => by
    have : ys = [] := List.Perm.nil_eq hp |>.symm
    subst this; rw [matchBag]; simp
  | x :: rest, ys, m, hd, hp, hinj, h => by
    simp only [DistinctList] at hd
    rw [matchBag]
    simp only [hp.length_eq, bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact matchBagFrom_scan d x rest inInputLine hd.1
      (fun zs m' hz hi hm => matchBag_perm d inInputLine rest zs m' hd.2 hz hi hm)
      ys [] [] m (hp.mem_iff.mp List.mem_cons_self) (by simp) (by simpa using hp) (by simpa using hinj) h

theorem value_refl (d : List String) (v : Option CValue) (m : Bindings) (hd : ∀ c, v = some c → Distinct c)
    (h : SelfBound m) : (tryEqual d v v m).1 = true := by
  unfold tryEqual equalContent
  match v with
  | none => rfl
  | some c => exact (equal_refl d c _ false (hd c rfl) (bindValues_self d c m h)).1

theorem bag_order_free (d : List String) (xs ys : List CValue) (m : Bindings) (inInputLine : Bool)
    (hd : DistinctList xs) (hp : xs.Perm ys) (hinj : FlattenInjective ys) (h : SelfBound m) :
    (equal d (.bag xs) (.bag ys) m inInputLine).1 = true := by
  rw [equal]
  have := matchBag_perm d inInputLine xs ys m hd hp hinj h
  split
  · rfl
  · rename_i e; rw [e] at this; cases this

/-- Whether the paired lines have the same type, place, and time. -/
def Placed (ids : Ids) (p : Pair) : Prop :=
  p.2.line.body.type = p.1.line.body.type ∧ samePlace ids p.1.line p.2.line = true ∧
    sameTime p.1.line p.2.line = true

mutual

theorem pairExactly_spec (c : Ctx) (ids : Ids) (d : List String) :
    ∀ (ss ts : List Out) (m : Bindings) (pairs : List Pair) (m' : Bindings),
      pairExactly c ids d ss ts m = some (pairs, m') →
      pairs.map (·.1) = ss ∧ (∃ r, (pairs.map (·.2) ++ r).Perm ts) ∧ ∀ p ∈ pairs, Placed ids p
  | [], ts, m, pairs, m', h => by
    rw [pairExactly] at h; cases h; exact ⟨rfl, ⟨ts, by simp⟩, by simp⟩
  | first :: rest, ts, m, pairs, m', h => by
    rw [pairExactly] at h
    exact pairExactly_go_spec c ids d first rest ts [] [] m pairs m' ts (by simp) h

theorem pairExactly_go_spec (c : Ctx) (ids : Ids) (d : List String) (first : Out) (rest : List Out) :
    ∀ (cands passed : List Out) (tried : List Value) (m : Bindings) (pairs : List Pair) (m' : Bindings)
      (ts : List Out), (passed.reverse ++ cands).Perm ts →
      pairExactly.go c ids d first rest cands passed tried m = some (pairs, m') →
      pairs.map (·.1) = first :: rest ∧ (∃ r, (pairs.map (·.2) ++ r).Perm ts) ∧ ∀ p ∈ pairs, Placed ids p
  | [], _, _, _, _, _, _, _, h => by rw [pairExactly.go] at h; cases h
  | t :: more, passed, tried, m, pairs, m', ts, hp, h => by
    rw [pairExactly.go] at h
    have hp' : ((t :: passed).reverse ++ more).Perm ts := by simpa using hp
    split at h
    · exact pairExactly_go_spec c ids d first rest more (t :: passed) tried m pairs m' ts hp' h
    · rename_i hplace
      dsimp only at h
      split at h
      · exact pairExactly_go_spec c ids d first rest more (t :: passed) tried m pairs m' ts hp' h
      · split at h
        · split at h
          · rename_i rp m'' e
            obtain ⟨h1, ⟨r, hr⟩, h3⟩ := pairExactly_spec c ids d rest (passed.reverse ++ more) _ rp m'' e
            cases h
            refine ⟨by simp [h1], ⟨r, ?_⟩, ?_⟩
            · have : (passed.reverse ++ more).Perm (passed.reverse ++ more) := List.Perm.refl _
              simp only [List.map_cons, List.cons_append]
              exact ((hr.cons t).trans (List.perm_middle.symm)).trans hp
            · intro p hp
              rcases List.mem_cons.mp hp with e | e
              · subst e
                simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hplace
                refine ⟨?_, ?_, ?_⟩ <;> simp_all
              · exact h3 p e
          · exact pairExactly_go_spec c ids d first rest more (t :: passed) _ m pairs m' ts hp' h
        · exact pairExactly_go_spec c ids d first rest more (t :: passed) _ m pairs m' ts hp' h

end

def SameName (st : St) (p : String × String) : Prop :=
  ∃ s t, st.openSnapshot.lookup p.1 = some s ∧ st.openTrace.lookup p.2 = some t ∧ s.name = t.name

mutual

theorem pairOpen_spec (st : St) :
    ∀ (ss ts : List String) (m : Bindings) (pairs : List (String × String)) (m' : Bindings),
      pairOpen st ss ts m = some (pairs, m') →
      pairs.map (·.1) = ss ∧ (pairs.map (·.2)).Perm ts ∧ ∀ p ∈ pairs, SameName st p
  | [], ts, m, pairs, m', h => by
    rw [pairOpen] at h
    split at h
    · rename_i e; cases h; simp only [List.isEmpty_iff] at e; subst e; simp
    · cases h
  | first :: rest, ts, m, pairs, m', h => by
    rw [pairOpen] at h
    exact pairOpen_go_spec st first rest ts [] [] m pairs m' ts (by simp) h

theorem pairOpen_go_spec (st : St) (first : String) (rest : List String) :
    ∀ (cands passed : List String) (tried : List (Option Value)) (m : Bindings) (pairs : List (String × String))
      (m' : Bindings) (ts : List String), (passed.reverse ++ cands).Perm ts →
      pairOpen.go st first rest cands passed tried m = some (pairs, m') →
      pairs.map (·.1) = first :: rest ∧ (pairs.map (·.2)).Perm ts ∧ ∀ p ∈ pairs, SameName st p
  | [], _, _, _, _, _, _, _, h => by rw [pairOpen.go] at h; cases h
  | id :: more, passed, tried, m, pairs, m', ts, hp, h => by
    rw [pairOpen.go] at h
    have hp' : ((id :: passed).reverse ++ more).Perm ts := by simpa using hp
    split at h
    · rename_i s t hs ht
      split at h
      · exact pairOpen_go_spec st first rest more (id :: passed) tried m pairs m' ts hp' h
      · rename_i hname
        dsimp only at h
        split at h
        · exact pairOpen_go_spec st first rest more (id :: passed) tried m pairs m' ts hp' h
        · split at h
          · split at h
            · rename_i rp m'' e
              obtain ⟨h1, hr, h3⟩ := pairOpen_spec st rest (passed.reverse ++ more) _ rp m'' e
              cases h
              refine ⟨by simp [h1], ?_, ?_⟩
              · simp only [List.map_cons]
                exact ((hr.cons id).trans (List.perm_middle.symm)).trans hp
              · intro p hp
                rcases List.mem_cons.mp hp with e | e
                · subst e
                  exact ⟨s, t, hs, ht, by simpa using hname⟩
                · exact h3 p e
            · exact pairOpen_go_spec st first rest more (id :: passed) _ m pairs m' ts hp' h
          · exact pairOpen_go_spec st first rest more (id :: passed) _ m pairs m' ts hp' h
    · exact pairOpen_go_spec st first rest more (id :: passed) tried m pairs m' ts hp' h

end

theorem steps_go_inputs : ∀ (ls : List (Option Line)) (i : Nat) (acc : List Out),
    ∃ ins : List Out, (steps.go ls i acc).map (·.input) = ins.map some ++ [none]
  | [], _, _ => ⟨[], by simp [steps.go]⟩
  | none :: ls, i, acc => by simpa [steps.go] using steps_go_inputs ls (i + 1) acc
  | some l :: ls, i, acc => by
    simp only [steps.go]
    split
    · exact steps_go_inputs ls (i + 1) _
    · obtain ⟨ins, h⟩ := steps_go_inputs ls (i + 1) []
      exact ⟨{ line := l, index := i + 1 } :: ins, by simp [h]⟩

theorem steps_inputs (ls : List (Option Line)) :
    ∃ ins : List Out, (steps ls).map (·.input) = ins.map some ++ [none] :=
  steps_go_inputs ls 0 []

theorem input_isSome_iff (ls : List (Option Line)) (k : Nat) :
    (((steps ls)[k]?).bind (·.input)).isSome ↔ k + 1 < (steps ls).length := by
  obtain ⟨ins, h⟩ := steps_inputs ls
  have hl : (steps ls).length = ins.length + 1 := by
    have := congrArg List.length h; simpa using this
  have hk : ((steps ls)[k]?).bind (·.input) = (ins.map some ++ [none])[k]?.join := by
    rw [← h]; simp only [List.getElem?_map]; cases (steps ls)[k]? <;> rfl
  rw [hk, hl]
  by_cases hlt : k < ins.length
  · rw [List.getElem?_append_left (by simpa using hlt)]
    simp [hlt]
  · rw [List.getElem?_append_right (by simpa using hlt)]
    by_cases he : k = ins.length
    · subst he; simp
    · have : k - ins.length ≠ 0 := by omega
      simp only [List.length_map, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff, this,
          not_false_eq_true, getElem?_neg, Option.join_none, Option.isSome_none, Bool.false_eq_true,
          Nat.add_lt_add_iff_right, false_iff, Nat.not_lt, ge_iff_le]; omega

def IsMismatch : Finding → Prop
  | .mismatch _ => True
  | .uncomparable _ => False

def BothSome (w : Option Window × Option Window × Option Out) : Prop :=
  ((w.1.bind (·.input)).isSome ∧ (w.2.1.bind (·.input)).isSome)

def BothNone (w : Option Window × Option Window × Option Out) : Prop :=
  (w.1.bind (·.input)) = none ∧ (w.2.1.bind (·.input)) = none

theorem aligned_prefix (c : Ctx) (lineCount : Nat) (malformed : Option Nat) :
    ∀ (L : List (Option Window × Option Window × Option Out)) (st : St),
      (∀ f ∈ (compareFrom c lineCount malformed L st).findings, IsMismatch f) →
      ∀ j (hj : j < L.length), (∀ i (hi : i < j), BothSome L[i]) → BothSome L[j] ∨ BothNone L[j]
  | [], _, _, j, hj, _ => absurd hj (Nat.not_lt_zero _)
  | (e, a, p) :: rest, st, h, j, hj, hprev => by
    rw [compareFrom] at h
    generalize hw : runWindow c st _ _ _ = w at h
    obtain ⟨found, st'⟩ := w
    have tail : ∀ f ∈ (compareInputs c lineCount malformed (e.bind (·.input)) (a.bind (·.input)) rest st').findings,
        IsMismatch f := fun f hf => h f (List.mem_append_right _ hf)
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, BothSome, BothNone]
      cases he : e.bind (·.input) <;> cases ha : a.bind (·.input) <;> rw [he, ha, compareInputs] at tail
      · right; exact ⟨rfl, rfl⟩
      · exact False.elim (tail _ List.mem_cons_self)
      · exact False.elim (tail _ List.mem_cons_self)
      · left; simp
    | succ j =>
      have h0 := hprev 0 (Nat.zero_lt_succ j)
      simp only [List.getElem_cons_zero, BothSome] at h0
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h0.1
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h0.2
      rw [hs, ht, compareInputs] at tail
      split at tail
      · exact False.elim (tail _ List.mem_cons_self)
      · simp only [List.getElem_cons_succ]
        exact aligned_prefix c lineCount malformed rest _ tail j (by simpa using hj)
          (fun i hi => by have := hprev (i + 1) (by omega); simpa using this)

theorem compareFrom_malformed (c : Ctx) (lineCount n : Nat) :
    ∀ (L : List (Option Window × Option Window × Option Out)) (st : St), (∀ w ∈ L, (w.2.1.bind (·.input)).isSome) →
      ∃ (ms : List Mismatch) (u : Uncomparable),
        (compareFrom c lineCount (some n) L st).findings = ms.map .mismatch ++ [.uncomparable u]
  | [], _, _ => ⟨[], .lineSchema n, by rw [compareFrom]; rfl⟩
  | (e, a, p) :: rest, st, h => by
    rw [compareFrom]
    generalize runWindow c st _ _ _ = w
    obtain ⟨found, st'⟩ := w
    suffices hs : ∃ (ms : List Mismatch) (u : Uncomparable),
        (compareInputs c lineCount (some n) (e.bind (·.input)) (a.bind (·.input)) rest st').findings =
          ms.map .mismatch ++ [.uncomparable u] by
      obtain ⟨ms, u, hs⟩ := hs
      exact ⟨found ++ ms, u, by simp [hs]⟩
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h _ List.mem_cons_self)
    simp only at ht
    rw [ht]
    cases e.bind (·.input) <;> rw [compareInputs]
    · exact ⟨[], _, rfl⟩
    · split
      · exact ⟨[], _, rfl⟩
      · exact compareFrom_malformed c lineCount n rest _ fun w hw => h w (List.mem_cons_of_mem _ hw)

theorem compare_malformed (snapshot lines : List (Option Line)) (n : Nat) (internal : Line → Bool) :
    ∃ (ms : List Mismatch) (u : Uncomparable),
      (Verify.compare snapshot lines (some n) internal).findings = ms.map .mismatch ++ [.uncomparable u] := by
  unfold Verify.compare
  apply compareFrom_malformed
  intro w hw
  simp only [List.mem_map, List.mem_range] at hw
  obtain ⟨k, hk, rfl⟩ := hw
  exact (input_isSome_iff lines k).mpr (by omega)

theorem inputs_align (snapshot lines : List (Option Line)) (malformed : Option Nat) (internal : Line → Bool)
    (h : ∀ f ∈ (Verify.compare snapshot lines malformed internal).findings, IsMismatch f) :
    malformed = none ∧ (steps snapshot).length = (steps lines).length := by
  have hm : malformed = none := by
    cases malformed with
    | none => rfl
    | some n =>
      obtain ⟨ms, u, hc⟩ := compare_malformed snapshot lines n internal
      exact False.elim (h (.uncomparable u) (by simp [hc]))
  subst hm
  refine ⟨rfl, ?_⟩
  unfold Verify.compare at h
  generalize hE : steps snapshot = E at h
  generalize hA : steps lines = A at h
  have hEi := input_isSome_iff snapshot
  have hAi := input_isSome_iff lines
  rw [hE] at hEi
  rw [hA] at hAi
  have hE1 : 1 ≤ E.length := by
    obtain ⟨ins, h⟩ := steps_inputs snapshot; rw [hE] at h
    have := congrArg List.length h; simp only [List.length_map, List.length_append, List.length_cons, List.length_nil,
        Nat.zero_add] at this; omega
  have hA1 : 1 ≤ A.length := by
    obtain ⟨ins, h⟩ := steps_inputs lines; rw [hA] at h
    have := congrArg List.length h; simp only [List.length_map, List.length_append, List.length_cons, List.length_nil,
        Nat.zero_add] at this; omega
  have P := aligned_prefix _ _ _ _ _ h
  have key : ∀ k, k < max E.length A.length → (∀ i < k, i + 1 < E.length ∧ i + 1 < A.length) →
      ((k + 1 < E.length) ↔ (k + 1 < A.length)) := by
    intro k hk hall
    have := P k (by simpa using hk) (fun i hi => by
      simp only [List.getElem_map, List.getElem_range, BothSome]
      have := hall i hi
      exact ⟨(hEi i).mpr this.1, (hAi i).mpr this.2⟩)
    simp only [List.getElem_map, List.getElem_range, BothSome, BothNone] at this
    rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => (hAi k).mp h2, fun _ => (hEi k).mp h1⟩
    · have n1 : ¬ k + 1 < E.length := fun hlt => by have := (hEi k).mpr hlt; simp [h1] at this
      have n2 : ¬ k + 1 < A.length := fun hlt => by have := (hAi k).mpr hlt; simp [h2] at this
      constructor <;> intro x <;> omega
  have hk : min E.length A.length - 1 < max E.length A.length := by omega
  have := key (min E.length A.length - 1) hk (fun i hi => by omega)
  omega

theorem compareFrom_shape (c : Ctx) (lineCount : Nat) (malformed : Option Nat) :
    ∀ (L : List (Option Window × Option Window × Option Out)) (st : St),
      ∃ (ms : List Mismatch) (u : Option Uncomparable),
        (compareFrom c lineCount malformed L st).findings = ms.map .mismatch ++ u.toList.map .uncomparable
  | [], _ => ⟨[], malformed.map .lineSchema, by rw [compareFrom]; cases malformed <;> rfl⟩
  | (e, a, p) :: rest, st => by
    rw [compareFrom]
    generalize runWindow c st _ _ _ = w
    obtain ⟨found, st'⟩ := w
    suffices h : ∃ (ms : List Mismatch) (u : Option Uncomparable),
        (compareInputs c lineCount malformed (e.bind (·.input)) (a.bind (·.input)) rest st').findings =
          ms.map .mismatch ++ u.toList.map .uncomparable by
      obtain ⟨ms, u, h⟩ := h
      exact ⟨found ++ ms, u, by simp [h]⟩
    cases e.bind (·.input) <;> cases a.bind (·.input) <;> rw [compareInputs]
    · exact ⟨[], none, rfl⟩
    · exact ⟨[], some _, rfl⟩
    · exact ⟨[], some _, rfl⟩
    · split
      · exact ⟨[], some _, rfl⟩
      · exact compareFrom_shape c lineCount malformed rest _

theorem obj_order_free (d : List String) (fs gs : List (String × CValue)) (m : Bindings) (inInputLine : Bool)
    (hd : Distinct (.obj fs)) (hp : fs.Perm gs) (h : SelfBound m) :
    (equal d (.obj fs) (.obj gs) m inInputLine).1 = true := by
  simp only [Distinct] at hd
  have hk : (fs.map (·.1)).Perm (gs.map (·.1)) := hp.map _
  have hn : (gs.map (·.1)).Nodup := hk.nodup_iff.mp hd.1
  have contains (xs ys : List String) (hp : xs.Perm ys) : (xs.all ys.contains) = true := by
    simp only [List.all_eq_true, List.contains_iff_mem]; exact fun x hx => hp.mem_iff.mp hx
  rw [equal]
  simp only [hk.length_eq, beq_self_eq_true, contains _ _ hk, contains _ _ hk.symm, Bool.and_self, ite_true]
  exact (equalFields_refl d fs gs m inInputLine hd.2 (fun k v hm => lookup_of_mem hn (hp.mem_iff.mp hm)) h).1

theorem matchLine_quiet (s : Line) (t : Out) (c : Ctx) (st : St) (ht : sameTime s t.line = true)
    (he : (tryEqual st.declared (c.compared s t.line).1 (c.compared s t.line).2 st.values).1 = true) :
    (((matchLine s t).run c).run st).2.findings = st.findings := by
  unfold matchLine
  split <;> simp_all [ReaderT.run, StateT.run, bind, ReaderT.bind, StateT.bind, pure, ReaderT.pure, StateT.pure, get,
    getThe, MonadStateOf.get, StateT.get, set, StateT.set, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    read, ReaderT.read, MonadReader.read, MonadReaderOf.read, readThe, liftM, monadLift, MonadLift.monadLift,
    MonadLiftT.monadLift]

theorem matchLine_same (s : Line) (t : Out) (c : Ctx) (st : St) (ht : sameTime s t.line = true)
    (hv : (c.compared s t.line).1 = (c.compared s t.line).2)
    (hd : ∀ v, (c.compared s t.line).1 = some v → Distinct v) (h : SelfBound st.values) :
    (((matchLine s t).run c).run st).2.findings = st.findings :=
  matchLine_quiet s t c st ht (by rw [← hv]; exact value_refl _ _ _ hd h)

theorem find?_of_mem : ∀ {gs : List (String × CValue)} {k : String} {v : CValue},
    (gs.map (·.1)).Nodup → (k, v) ∈ gs → (gs.find? (·.1 == k)).map (·.2) = some v
  | [], _, _, _, h => absurd h List.not_mem_nil
  | (a, b) :: gs, k, v, hn, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hn
    rcases List.mem_cons.mp h with e | e
    · cases e; simp
    · have hka : a ≠ k := fun hk => hn.1 (k, v) e hk.symm
      simp [List.find?, beq_eq_false_iff_ne.mpr hka, find?_of_mem hn.2 e]

theorem at?_perm {fs gs : List (String × CValue)} (hn : (gs.map (·.1)).Nodup) (hp : fs.Perm gs) {k : String}
    {v : CValue} (h : (CValue.obj fs).at? k = some v) : (CValue.obj gs).at? k = some v := by
  simp only [CValue.at?, Option.map_eq_some_iff] at h ⊢
  obtain ⟨p, hf, rfl⟩ := h
  have hk : p.1 = k := by simpa using List.find?_some hf
  have hm : (k, p.2) ∈ gs := hp.mem_iff.mp (hk ▸ List.mem_of_find?_eq_some hf)
  simpa using find?_of_mem hn hm

theorem bindValues_perm (d : List String) (fs gs : List (String × CValue)) (m : Bindings)
    (hd : Distinct (.obj fs)) (hp : fs.Perm gs) (h : SelfBound m) :
    SelfBound (bindValues d (some (.obj fs)) (some (.obj gs)) m) := by
  simp only [Distinct] at hd
  have hn : (gs.map (·.1)).Nodup := (hp.map _).nodup_iff.mp hd.1
  rw [bindValues]
  · simp only [CValue.isPlain, Bool.and_self, ite_true]
    apply foldl_preserve _ _ _ _ _ h
    rintro b ⟨k, hk⟩ _ hb
    dsimp only
    split
    · rename_i sv hs
      rw [at?_perm hn hp hs]
      exact bindValues_self d sv b hb
    · exact hb
  · intro v e; cases e

theorem tryEqual_obj_perm (d : List String) (fs gs : List (String × CValue)) (m : Bindings)
    (hd : Distinct (.obj fs)) (hp : fs.Perm gs) (h : SelfBound m) :
    (tryEqual d (some (.obj fs)) (some (.obj gs)) m).1 = true := by
  unfold tryEqual equalContent
  exact obj_order_free d fs gs _ false hd hp (bindValues_perm d fs gs m hd hp h)

theorem matchLine_permuted (s : Line) (t : Out) (c : Ctx) (st : St) (fs gs : List (String × CValue))
    (ht : sameTime s t.line = true) (hc : c.compared s t.line = (some (.obj fs), some (.obj gs)))
    (hd : Distinct (.obj fs)) (hp : fs.Perm gs) (h : SelfBound st.values) :
    (((matchLine s t).run c).run st).2.findings = st.findings :=
  matchLine_quiet s t c st ht (by rw [hc]; exact tryEqual_obj_perm _ _ _ _ hd hp h)

end Tazuna.Thm.Verify.Compare
