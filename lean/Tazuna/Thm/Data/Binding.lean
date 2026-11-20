import Tazuna.Data.Binding
import Tazuna.Thm.Data.Renaming
import Tazuna.Thm.Data.List
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Data.Binding

open Tazuna.Data
open Tazuna.Thm.Data.Renaming
open Tazuna.Thm.Data.List (lookup_of_mem mem_of_lookup)

/-! ## Sets of states -/

theorem mem_limited {σ : Type} {same : σ → σ → Bool} {states out : List σ} (h : limited same states = some out)
    {x : σ} (hx : x ∈ out) : x ∈ states := by
  unfold limited at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    have : ∀ (acc : List σ), (∀ y ∈ acc, y ∈ states) → ∀ (rest : List σ), (∀ y ∈ rest, y ∈ states) →
        ∀ y ∈ rest.foldl (fun acc s => if acc.any (same s) then acc else acc ++ [s]) acc, y ∈ states := by
      intro acc hacc rest
      induction rest generalizing acc with
      | nil => intro _ y hy; exact hacc y hy
      | cons r rest ih =>
        intro hrest
        simp only [List.foldl_cons]
        apply ih
        · split
          · exact hacc
          · intro y hy
            rcases List.mem_append.mp hy with hy | hy
            · exact hacc y hy
            · simp at hy; subst hy; exact hrest _ List.mem_cons_self
        · exact fun y hy => hrest y (List.mem_cons_of_mem _ hy)
    exact this [] (by simp) states (fun _ h => h) x hx

theorem mem_of_mapM {α β : Type} {f : α → Option β} : ∀ {l : List α} {out : List β}, l.mapM f = some out →
    ∀ y ∈ out, ∃ x ∈ l, f x = some y
  | [], out, h => by simp at h; subst h; simp
  | x :: l, out, h => by
    rw [List.mapM_cons] at h
    cases hz : f x with
    | none => simp [hz] at h
    | some z =>
      cases hrest : l.mapM f with
      | none => simp [hz, hrest] at h
      | some rest =>
        simp only [hz, hrest, bind, Option.bind, pure] at h
        cases h
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x, List.mem_cons_self, hz⟩
        · obtain ⟨x', hx', e⟩ := mem_of_mapM hrest y hy
          exact ⟨x', List.mem_cons_of_mem _ hx', e⟩

theorem mem_expand {σ τ : Type} {same : τ → τ → Bool} {states : List σ} {next : σ → Option (List τ)}
    {out : List τ} (h : expand same states next = some out) {y : τ} (hy : y ∈ out) :
    ∃ st ∈ states, ∃ ys, next st = some ys ∧ y ∈ ys := by
  unfold expand at h
  simp only [bind, Option.bind] at h
  split at h
  · cases h
  · rename_i all hall
    obtain ⟨ys, hys, hyys⟩ := List.mem_flatten.mp (mem_limited h hy)
    obtain ⟨st, hst, e⟩ := mem_of_mapM hall ys hys
    exact ⟨st, hst, ys, e, hyys⟩

theorem mem_andThen {b : Binding} {m : Matches b} {f : (c : Binding) → Matches c} {out : List (From b)}
    (h : m.andThen f = some out) {c : From b} (hc : c ∈ out) :
    ∃ l, m = some l ∧ ∃ c₁ ∈ l, ∃ l₂, f c₁.val = some l₂ ∧ ∃ c₂ ∈ l₂, c.val = c₂.val := by
  unfold Matches.andThen at h
  cases hm : m with
  | none => simp [hm, bind, Option.bind] at h
  | some l =>
    simp only [hm, bind, Option.bind] at h
    obtain ⟨c₁, hc₁, ys, hys, hcys⟩ := mem_expand h hc
    cases hf : f c₁.val with
    | none => simp [hf] at hys
    | some l₂ =>
      simp only [hf, Option.map_some, Option.some.injEq] at hys
      subst hys
      obtain ⟨c₂, hc₂, rfl⟩ := List.mem_map.mp hcys
      exact ⟨l, rfl, c₁, hc₁, l₂, hf, c₂, hc₂, rfl⟩

/-! ## Values -/

/--
`b` relates snapshot string `s` to implementation string `t` as matchValue compares them: as a pair of `b` in the domain
of `s`, or as one string of domain "", which compares equal to itself without entering the binding.
-/
def BoundBy (dom : String → String) (b : Binding) (s t : String) : Prop :=
  ((dom s, s), (dom s, t)) ∈ b.pairs ∨ (s = t ∧ dom s = "")

theorem BoundBy.mono {dom : String → String} {b c : Binding} (h : b.Extends c) {s t : String} :
    BoundBy dom b s t → BoundBy dom c s t
  | .inl hp => .inl (h _ hp)
  | .inr e => .inr e

theorem bindString_bound {fresh : Bool} {b : Binding} {s t : Bound} {c : { c : Binding // b.Extends c }}
    (h : b.bindString fresh s t = some c) : (s, t) ∈ c.val.pairs ∨ (s = t ∧ s.1 = "") := by
  unfold Binding.bindString at h
  split at h
  · split at h
    · rename_i hp; cases h; exact .inl hp
    · cases h
  · split at h
    · rename_i hf; cases h
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hf
      exact .inr ⟨hf.1.2, hf.2⟩
    · split at h
      · cases h
      · split at h
        · cases h; exact .inl (by simp)
        · cases h

theorem bind_bound {v : Values} {b : Binding} {s t : String} {out : List (From b)} (h : v.bind b s t = some out) :
    ∀ c ∈ out, BoundBy v.domain c.val s t := by
  intro c hc
  unfold Values.bind Matches.one at h
  split at h
  · rename_i c' hc'
    cases h
    simp only [List.mem_singleton] at hc
    subst hc
    rcases bindString_bound hc' with hp | ⟨e, hd⟩
    · exact .inl hp
    · cases e; exact .inr ⟨rfl, hd⟩
  · cases h; cases hc

mutual

/-- No object of the value has two fields with one key, as JSON objects that verify reads. -/
inductive Distinct : CValue → Prop
  | leaf (x : Value) : Distinct (.leaf x)
  | ref (e s : String) : Distinct (.ref e s)
  | arr {xs : List CValue} : DistinctList xs → Distinct (.arr xs)
  | runs {xs : List CValue} : DistinctList xs → Distinct (.runs xs)
  | bag {xs : List CValue} : DistinctList xs → Distinct (.bag xs)
  | obj {fs : List (String × CValue)} : (fs.map (·.1)).Nodup → DistinctFields fs → Distinct (.obj fs)

inductive DistinctList : List CValue → Prop
  | nil : DistinctList []
  | cons {x : CValue} {xs : List CValue} : Distinct x → DistinctList xs → DistinctList (x :: xs)

inductive DistinctFields : List (String × CValue) → Prop
  | nil : DistinctFields []
  | cons {k : String} {x : CValue} {fs : List (String × CValue)} : Distinct x → DistinctFields fs →
      DistinctFields ((k, x) :: fs)

end

theorem DistinctList.mem : {xs : List CValue} → DistinctList xs → {x : CValue} → x ∈ xs → Distinct x
  | _, .cons hd _, _, .head _ => hd
  | _, .cons _ hl, _, .tail _ hx => DistinctList.mem hl hx

theorem DistinctFields.mem : {fs : List (String × CValue)} → DistinctFields fs → {p : String × CValue} → p ∈ fs →
    Distinct p.2
  | _, .cons hd _, _, .head _ => hd
  | _, .cons _ hl, _, .tail _ hp => DistinctFields.mem hl hp

theorem nodup_of_map {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup) : l.Nodup :=
  List.Pairwise.of_map f (fun _ _ h e => h (congrArg f e)) h

/-! ## Bags -/

theorem perm_pick {α : Type} : ∀ {L : List (α × Nat)}, (L.map (·.2)).Nodup → ∀ {y : α} {j : Nat}, (y, j) ∈ L →
    L.Perm ((y, j) :: L.filter fun p => !(p.2 == j))
  | p :: L, hn, y, j, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp h with e | h
    · subst e
      have : L.filter (fun p => !(p.2 == j)) = L := by
        refine List.filter_eq_self.mpr fun q hq => ?_
        have : q.2 ≠ j := fun e => hn.1 ⟨q, hq, e⟩
        simpa using this
      simp [this]
    · have hne : p.2 ≠ j := fun e => hn.1 ⟨(y, j), h, e.symm⟩
      have ih := perm_pick hn.2 h
      have hb : (!(p.2 == j)) = true := by simp [hne]
      simp only [List.filter_cons, hb, ↓reduceIte]
      exact (ih.cons p).trans (List.Perm.swap _ _ _)

theorem RenamedList.snoc {R : String → String → Prop} : ∀ {xs ys : List CValue} {x y : CValue}, RenamedList R xs ys →
    Renamed R x y → RenamedList R (xs ++ [x]) (ys ++ [y])
  | _, _, _, _, .nil, h => .cons h .nil
  | _, _, _, _, .cons h hl, h' => .cons h (RenamedList.snoc hl h')

theorem foldlM_inv {α σ : Type} (step : σ → α → Option σ) (I : List α → σ → Prop)
    (hstep : ∀ pre st x st', I pre st → step st x = some st' → I (pre ++ [x]) st') :
    ∀ (l pre : List α) (st st' : σ), I pre st → l.foldlM step st = some st' → I (pre ++ l) st'
  | [], pre, st, st', hi, h => by simp at h; subst h; simpa using hi
  | x :: l, pre, st, st', hi, h => by
    rw [List.foldlM_cons] at h
    cases hs : step st x with
    | none => simp [hs, bind, Option.bind] at h
    | some st₁ =>
      simp only [hs, bind, Option.bind] at h
      have := foldlM_inv step I hstep l (pre ++ [x]) st₁ st' (hstep pre st x st₁ hi hs) h
      simpa using this

/-- The elements of `ys` whose places `used` does not hold. -/
def unused (ys : List CValue) (used : List Nat) : List (CValue × Nat) :=
  ys.zipIdx.filter fun p => !used.contains p.2

theorem unused_nodup (ys : List CValue) (used : List Nat) : ((unused ys used).map (·.2)).Nodup := by
  unfold unused
  have h : (ys.zipIdx.map (·.2)).Nodup := by rw [List.zipIdx_map_snd]; exact List.nodup_range' ..
  exact (List.filter_sublist.map _).nodup h

theorem unused_snoc (ys : List CValue) (used : List Nat) (j : Nat) :
    unused ys (used ++ [j]) = (unused ys used).filter fun p => !(p.2 == j) := by
  unfold unused
  rw [List.filter_filter]
  congr 1
  funext p
  by_cases h : p.2 = j <;> simp [h]

/-- What the pairing of a bag holds after the elements `pre`: they rename to the chosen elements under the binding, and
the chosen elements and the unused ones are the bag's elements. -/
def BagPaired (dom : String → String) (ys pre : List CValue) (st : Binding × List Nat) : Prop :=
  ∃ ys', RenamedList (BoundBy dom st.1) pre ys' ∧ (ys' ++ (unused ys st.2).map (·.1)).Perm ys ∧
    ys'.length = pre.length

theorem bagPaired_start (dom : String → String) (b : Binding) (ys : List CValue) :
    BagPaired dom ys [] (b, []) := by
  refine ⟨[], .nil, ?_, rfl⟩
  have : (unused ys []) = ys.zipIdx := List.filter_eq_self.mpr (by simp)
  rw [this, List.nil_append]
  exact .of_eq (List.zipIdx_map_fst 0 ys)

theorem bagPaired_step {dom : String → String} {ys pre : List CValue} {b c : Binding} (hbc : b.Extends c)
    {used : List Nat} {x y : CValue} {j : Nat} (hp : BagPaired dom ys pre (b, used)) (hy : (y, j) ∈ unused ys used)
    (hr : Renamed (BoundBy dom c) x y) : BagPaired dom ys (pre ++ [x]) (c, used ++ [j]) := by
  obtain ⟨ys', hl, hperm, hlen⟩ := hp
  refine ⟨ys' ++ [y], RenamedList.snoc (RenamedList.mono (fun _ _ => BoundBy.mono hbc) hl) hr, ?_, by simp [hlen]⟩
  have hpick := (perm_pick (unused_nodup ys used) hy).map (·.1)
  rw [unused_snoc]
  refine List.Perm.trans ?_ hperm
  simp only [List.append_assoc, List.singleton_append]
  exact (hpick.append_left ys').symm

mutual

/--
Every binding under which matchValue compares two values equal relates them by `Renamed`: keys as the binding pairs
them, bags and objects after reordering.
-/
@[guarantee] theorem matchValue_renamed (v : Values) (b : Binding) (x y : CValue) (hx : Distinct x) (hy : Distinct y)
    {out : List (From b)} (h : matchValue v b x y = some out) : ∀ c ∈ out, Renamed (BoundBy v.domain c.val) x y := by
  intro c hc
  match x, y, hx, hy with
  | .ref _ s, .ref _ t, _, _ =>
    rw [matchValue] at h
    exact .ref (bind_bound h c hc)
  | .leaf a, .leaf a', _, _ =>
    rw [matchValue] at h
    split at h
    · rename_i he
      cases beq_iff_eq.mp he
      cases h
      simp only [List.mem_singleton] at hc
      exact .leaf
    · cases h; cases hc
  | .arr xs, .arr ys, .arr hx, .arr hy =>
    rw [matchValue] at h
    exact .arr (matchList_renamed v b xs ys hx hy h c hc)
  | .runs xs, .runs ys, .runs hx, .runs hy =>
    rw [matchValue] at h
    exact .runs (matchList_renamed v b xs ys hx hy h c hc)
  | .obj fs, .obj gs, .obj hfn hx, .obj hgn hy =>
    rw [matchValue] at h
    split at h
    · rename_i hk
      obtain ⟨gs', hr, hkeys, hlook⟩ := matchFields_renamed v b fs gs hx hy h c hc
      refine .obj hr ?_
      have hn' : gs'.Nodup := nodup_of_map (hkeys ▸ hfn)
      have hn : gs.Nodup := nodup_of_map hgn
      refine (List.perm_ext_iff_of_nodup hn' hn).mpr fun p => ⟨fun hp => mem_of_lookup (hlook p hp), fun hp => ?_⟩
      simp only [sameKeys, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hk
      have hk' : p.1 ∈ gs'.map (·.1) := hkeys ▸ hk.2 p.1 (List.mem_map.mpr ⟨p, hp, rfl⟩)
      obtain ⟨q, hq, e⟩ := List.mem_map.mp hk'
      have h1 := hlook q hq
      rw [e, lookup_of_mem hgn hp] at h1
      have : q = p := Prod.ext e (Option.some.inj h1).symm
      exact this ▸ hq
    · cases h; cases hc
  | .bag xs, .bag ys, .bag hx, .bag hy =>
    rw [matchValue] at h
    split at h
    · rename_i hlen
      unfold matchBag at h
      simp only [bind, Option.bind] at h
      split at h
      · cases h
      · rename_i paired hpaired
        obtain ⟨st, hst, rfl⟩ := List.mem_map.mp (mem_limited h hc)
        have hinv := foldlM_inv _ (fun pre states => ∀ st ∈ states, BagPaired v.domain ys (pre.map (·.1)) (st.1.val, st.2))
          (fun pre states x states' hi hs => by
            intro st' hst'
            obtain ⟨⟨c₀, used⟩, hst₀, ys₀, hnext, hys₀⟩ := mem_expand hs hst'
            split at hnext
            · cases hnext
            · rename_i all hall
              cases hnext
              obtain ⟨l, hl, hst'l⟩ := List.mem_flatten.mp hys₀
              obtain ⟨⟨y, j⟩, hyj, hm⟩ := mem_of_mapM hall l hl
              cases hmv : matchValue v c₀.val x.1 y with
              | none => simp [hmv] at hm
              | some ds =>
                simp only [hmv, Option.map_some, Option.some.injEq] at hm
                subst hm
                obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hst'l
                obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hd
                have hyu : (y, j) ∈ unused ys used := by simpa [unused] using hyj
                have hyd : Distinct y := DistinctList.mem hy (List.mem_of_getElem? ((List.mem_zipIdx_iff_getElem?.mp
                  (List.mem_filter.mp hyu).1)))
                have hr := matchValue_renamed v c₀.val x.1 y (DistinctList.mem hx x.2) hyd hmv d' hd'
                simpa using bagPaired_step d'.property (hi _ hst₀) hyu hr)
          xs.attach [] [(⟨b, .refl b⟩, [])] paired
          (by intro st hst; simp at hst; subst hst; exact bagPaired_start _ _ _) hpaired
        obtain ⟨ys', hl, hperm, hlen'⟩ := hinv st hst
        simp only [List.nil_append, List.attach_map_subtype_val] at hl hlen'
        have hu : (unused ys st.2).map (·.1) = [] := by
          have := hperm.length_eq
          simp only [List.length_append] at this
          have : ys.length = xs.length := (beq_iff_eq.mp hlen).symm
          exact List.eq_nil_of_length_eq_zero (by omega)
        rw [hu, List.append_nil] at hperm
        exact .bag hl hperm
    · cases h; cases hc
  | .leaf _, .ref _ _, _, _ | .leaf _, .arr _, _, _ | .leaf _, .obj _, _, _ | .leaf _, .bag _, _, _
  | .leaf _, .runs _, _, _ | .ref _ _, .leaf _, _, _ | .ref _ _, .arr _, _, _ | .ref _ _, .obj _, _, _
  | .ref _ _, .bag _, _, _ | .ref _ _, .runs _, _, _ | .arr _, .leaf _, _, _ | .arr _, .ref _ _, _, _
  | .arr _, .obj _, _, _ | .arr _, .bag _, _, _ | .arr _, .runs _, _, _ | .obj _, .leaf _, _, _
  | .obj _, .ref _ _, _, _ | .obj _, .arr _, _, _ | .obj _, .bag _, _, _ | .obj _, .runs _, _, _
  | .bag _, .leaf _, _, _ | .bag _, .ref _ _, _, _ | .bag _, .arr _, _, _ | .bag _, .obj _, _, _
  | .bag _, .runs _, _, _ | .runs _, .leaf _, _, _ | .runs _, .ref _ _, _, _ | .runs _, .arr _, _, _
  | .runs _, .obj _, _, _ | .runs _, .bag _, _, _ =>
    rw [matchValue] at h
    all_goals first | (cases h; cases hc) | (intros; simp_all)
termination_by sizeOf x
decreasing_by all_goals first | decreasing_tactic | (simp_wf; have := List.sizeOf_lt_of_mem x.2; omega)

theorem matchList_renamed (v : Values) (b : Binding) (xs ys : List CValue) (hx : DistinctList xs)
    (hy : DistinctList ys) {out : List (From b)} (h : matchList v b xs ys = some out) :
    ∀ c ∈ out, RenamedList (BoundBy v.domain c.val) xs ys := by
  intro c hc
  match xs, ys, hx, hy with
  | [], [], _, _ => exact .nil
  | x :: xs, y :: ys, .cons hx hxs, .cons hy hys =>
    rw [matchList] at h
    obtain ⟨l, hl, c₁, hc₁, l₂, hl₂, c₂, hc₂, e⟩ := mem_andThen h hc
    have h₁ := matchValue_renamed v b x y hx hy hl c₁ hc₁
    have h₂ := matchList_renamed v c₁.val xs ys hxs hys hl₂ c₂ hc₂
    rw [e]
    exact .cons (Renamed.mono (fun _ _ => BoundBy.mono c₂.property) h₁) h₂
  | [], _ :: _, _, _ | _ :: _, [], _, _ =>
    rw [matchList] at h
    all_goals first | (cases h; cases hc) | (intros; simp_all)
termination_by sizeOf xs
decreasing_by all_goals decreasing_tactic

theorem matchFields_renamed (v : Values) (b : Binding) (fs gs : List (String × CValue)) (hx : DistinctFields fs)
    (hy : DistinctFields gs) {out : List (From b)} (h : matchFields v b fs gs = some out) :
    ∀ c ∈ out, ∃ gs', RenamedFields (BoundBy v.domain c.val) fs gs' ∧ gs'.map (·.1) = fs.map (·.1) ∧
      ∀ p ∈ gs', gs.lookup p.1 = some p.2 := by
  intro c hc
  match fs, hx with
  | [], _ => exact ⟨[], .nil, rfl, by simp⟩
  | (k, x) :: fs, .cons hx hfs =>
    rw [matchFields] at h
    split at h
    · rename_i y hk
      obtain ⟨l, hl, c₁, hc₁, l₂, hl₂, c₂, hc₂, e⟩ := mem_andThen h hc
      have h₁ := matchValue_renamed v b x y hx (DistinctFields.mem hy (mem_of_lookup hk)) hl c₁ hc₁
      obtain ⟨gs', hr, hkeys, hlook⟩ := matchFields_renamed v c₁.val fs gs hfs hy hl₂ c₂ hc₂
      rw [e]
      refine ⟨(k, y) :: gs', .cons (Renamed.mono (fun _ _ => BoundBy.mono c₂.property) h₁) hr, by simp [hkeys], ?_⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hk
      · exact hlook p hp
    · cases h; cases hc
termination_by sizeOf fs
decreasing_by all_goals decreasing_tactic

end

/--
When a binding pairs no value of domain "", the strings it relates as matchValue compares them are the strings it
renames (StrRenames), the relation that renamed_refl, renamed_symm and renamed_trans prove an equivalence.
-/
theorem boundBy_strRenames {dom : String → String} {c : Binding} (hc : ∀ p ∈ c.pairs, p.1.1 ≠ "" ∧ p.2.1 ≠ "")
    {s t : String} : BoundBy dom c s t → StrRenames dom c.pairs s t
  | .inl hp => .inl hp
  | .inr ⟨e, hd⟩ => by
    subst e
    refine .inr ⟨rfl, fun hm => ?_, fun hm => ?_⟩
    · obtain ⟨p, hp, e⟩ := List.mem_map.mp hm
      exact (hc p hp).1 (by rw [e]; exact hd)
    · obtain ⟨p, hp, e⟩ := List.mem_map.mp hm
      exact (hc p hp).2 (by rw [e]; exact hd)

/-- matchValue_renamed for a binding that pairs no value of domain "", in the relation of Renaming. -/
@[guarantee] theorem matchValue_strRenamed {v : Values} {b : Binding} {x y : CValue} (hx : Distinct x) (hy : Distinct y)
    {out : List (From b)} (h : matchValue v b x y = some out) {c : From b} (hc : c ∈ out)
    (hblank : ∀ p ∈ c.val.pairs, p.1.1 ≠ "" ∧ p.2.1 ≠ "") : Renamed (StrRenames v.domain c.val.pairs) x y :=
  Renamed.mono (fun _ _ => boundBy_strRenames hblank) (matchValue_renamed v b x y hx hy h c hc)

end Tazuna.Thm.Data.Binding
