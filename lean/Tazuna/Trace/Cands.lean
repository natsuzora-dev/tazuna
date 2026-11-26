import Tazuna.Trace.Pairs

/-! The bindings verify still holds possible: blocks of keys and names, where a block's keys are its names in some one
to one way (`Cands.Has`). A block of one key is a decided binding. Verify narrows the blocks as lines tell keys apart
(`refineBy`, exact by `refineBy_has`) and splits a key off when it must choose (`narrow`, exact by `narrow_has`), so it
never enumerates the bindings of alike ids a window shows; a later line that names one of them decides it then. -/

namespace Tazuna.Trace

open Tazuna.Ir

theorem inj_of_nodup_map {α β : Type} {f : α → β} : {l : List α} → (l.map f).Nodup →
    ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b
  | [], _, _, ha, _, _, _ => absurd ha (by simp)
  | x :: l, h, a, ha, b, hb, hab => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    have h1 := h.1
    by_cases hax : a = x <;> by_cases hbx : b = x
    · rw [hax, hbx]
    · subst hax; exact absurd hab.symm (h1 b ((List.mem_cons.1 hb).resolve_left hbx))
    · subst hbx; exact absurd hab (h1 a ((List.mem_cons.1 ha).resolve_left hax))
    · exact inj_of_nodup_map h.2 a ((List.mem_cons.1 ha).resolve_left hax) b ((List.mem_cons.1 hb).resolve_left hbx) hab

theorem nodup_map_of_inj {α β : Type} {f : α → β} : {l : List α} → l.Nodup → (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) →
    (l.map f).Nodup
  | [], _, _ => .nil
  | x :: l, h, hi => by
    simp only [List.nodup_cons] at h
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun a ha he => h.1 (by have := hi a (by simp [ha]) x (by simp) he; subst this; exact ha),
      nodup_map_of_inj h.2 fun a ha b hb => hi a (by simp [ha]) b (by simp [hb])⟩

/-- A list without repeats inside another of the same length without repeats holds the same items. -/
theorem perm_of_subset {α : Type} {a b : List α} (ha : a.Nodup) (hb : b.Nodup) (hs : a ⊆ b)
    (hl : a.length = b.length) : a.Perm b := by
  classical
  refine (List.perm_ext_iff_of_nodup ha hb).2 fun x => ⟨fun h => hs h, fun h => ?_⟩
  by_cases hx : x ∈ a
  · exact hx
  exfalso
  have : a ⊆ b.erase x := fun y hy => (List.mem_erase_of_ne (by rintro rfl; exact hx hy)).2 (hs hy)
  have := ha.length_le_of_subset this
  rw [List.length_erase_of_mem h] at this
  have : 0 < b.length := List.length_pos_of_mem h
  omega

abbrev Block := List Key × List Name

/-- The bindings verify still holds possible. -/
structure Cands where
  blocks : List Block := []

namespace Cands

def keys (C : Cands) : List Key := C.blocks.flatMap (·.1)

def names (C : Cands) : List Name := C.blocks.flatMap (·.2)

/-- No key or name lies in two blocks or twice in one, a block has as many keys as names, and ids go with id names and
wire ids with wire names. -/
structure Ok (C : Cands) : Prop where
  keys : C.keys.Nodup
  names : C.names.Nodup
  len : ∀ b ∈ C.blocks, b.1.length = b.2.length
  space : ∀ b ∈ C.blocks, ∀ k ∈ b.1, ∀ s ∈ b.2, k.isWire = s.isWire

/-- The binding `β` is one the blocks hold possible: each block's keys are its names. -/
def Has (β : Key → Name) (C : Cands) : Prop := ∀ b ∈ C.blocks, (b.1.map β).Perm b.2

variable {C : Cands} {β : Key → Name}

theorem perm_flatMap {bs : List Block} (h : ∀ b ∈ bs, (b.1.map β).Perm b.2) :
    ((bs.flatMap (·.1)).map β).Perm (bs.flatMap (·.2)) := by
  induction bs with
  | nil => exact .refl _
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.map_append]
    exact (h b (by simp)).append (ih fun b' hb' => h b' (by simp [hb']))

theorem Has.perm (h : C.Has β) : (C.keys.map β).Perm C.names := perm_flatMap h

theorem Has.inj (hC : C.Ok) (h : C.Has β) : ∀ a ∈ C.keys, ∀ b ∈ C.keys, β a = β b → a = b :=
  inj_of_nodup_map ((h.perm).nodup_iff.2 hC.names)

theorem Has.mem (h : C.Has β) {k : Key} (hk : k ∈ C.keys) : β k ∈ C.names :=
  h.perm.mem_iff.1 (List.mem_map_of_mem hk)

end Cands

theorem mem_flatMap_unique {α γ : Type} {f : α → List γ} : {bs : List α} → (bs.flatMap f).Nodup →
    ∀ {b b' : α}, b ∈ bs → b' ∈ bs → ∀ {x : γ}, x ∈ f b → x ∈ f b' → b = b'
  | [], _, _, _, hb, _, _, _, _ => absurd hb (by simp)
  | c :: bs, h, b, b', hb, hb', x, hx, hx' => by
    rw [List.flatMap_cons, List.nodup_append] at h
    obtain ⟨_, h2, h3⟩ := h
    have hin : ∀ {d}, d ∈ bs → x ∈ f d → x ∈ bs.flatMap f := fun hd hxd => List.mem_flatMap.2 ⟨_, hd, hxd⟩
    by_cases hbc : b = c <;> by_cases hbc' : b' = c
    · rw [hbc, hbc']
    · subst hbc; exact absurd rfl (h3 x hx x (hin ((List.mem_cons.1 hb').resolve_left hbc') hx'))
    · subst hbc'; exact absurd rfl (h3 x hx' x (hin ((List.mem_cons.1 hb).resolve_left hbc) hx))
    · exact mem_flatMap_unique h2 ((List.mem_cons.1 hb).resolve_left hbc) ((List.mem_cons.1 hb').resolve_left hbc')
        hx hx'

theorem mapM_forall2 {α γ : Type} {f : α → Option γ} : {xs : List α} → {ys : List γ} → xs.mapM f = some ys →
    Forall2 (fun x y => f x = some y) xs ys
  | [], ys, h => by simp at h; subst h; trivial
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys', rfl⟩ := h
    exact ⟨hy, mapM_forall2 hys'⟩

namespace Cands

variable {C : Cands} {β : Key → Name}

theorem Ok.block_unique (hC : C.Ok) {b b' : Block} (hb : b ∈ C.blocks) (hb' : b' ∈ C.blocks) {k : Key} (hk : k ∈ b.1)
    (hk' : k ∈ b'.1) : b = b' :=
  mem_flatMap_unique hC.keys hb hb' hk hk'

theorem mem_keys {b : Block} (hb : b ∈ C.blocks) {k : Key} (hk : k ∈ b.1) : k ∈ C.keys :=
  List.mem_flatMap.2 ⟨b, hb, hk⟩

theorem mem_names {b : Block} (hb : b ∈ C.blocks) {s : Name} (hs : s ∈ b.2) : s ∈ C.names :=
  List.mem_flatMap.2 ⟨b, hb, hs⟩

/-- The blocks with key `k` bound to name `s`: the block that holds them splits into the pair and the rest. -/
def narrow (C : Cands) (k : Key) (s : Name) : Cands :=
  ⟨C.blocks.flatMap fun b =>
    if b.1.contains k then ([k], [s]) :: if (b.1.erase k).isEmpty then [] else [(b.1.erase k, b.2.erase s)]
    else [b]⟩

/-- Binding a key to one of its block's names keeps the bindings that bind it so, and only those. -/
theorem narrow_has (hC : C.Ok) {b : Block} (hb : b ∈ C.blocks) {k : Key} {s : Name} (hk : k ∈ b.1) (hs : s ∈ b.2) :
    (C.narrow k s).Has β ↔ C.Has β ∧ β k = s := by
  have only : ∀ b' ∈ C.blocks, k ∈ b'.1 → b' = b := fun b' hb' hk' => hC.block_unique hb' hb hk' hk
  have hb1 : b.1.Perm (k :: b.1.erase k) := List.perm_cons_erase hk
  have hb2 : b.2.Perm (s :: b.2.erase s) := List.perm_cons_erase hs
  unfold Has narrow
  simp only [List.mem_flatMap]
  constructor
  · intro h
    have hks : β k = s := by
      have := h ([k], [s]) ⟨b, hb, by simp [hk]⟩
      simpa using this
    refine ⟨fun b' hb' => ?_, hks⟩
    by_cases hk' : k ∈ b'.1
    · obtain rfl := only b' hb' hk'
      have hrest : ((b'.1.erase k).map β).Perm (b'.2.erase s) := by
        by_cases he : (b'.1.erase k).isEmpty
        · have he' : b'.1.erase k = [] := List.isEmpty_iff.1 he
          have hl := hC.len b' hb'
          rw [hb1.length_eq, hb2.length_eq, he'] at hl
          simp only [List.length_cons, List.length_nil] at hl
          rw [he', List.eq_nil_of_length_eq_zero (show (b'.2.erase s).length = 0 by omega)]; simp
        · exact h (b'.1.erase k, b'.2.erase s) ⟨b', hb', by simp [hk', he]⟩
      exact (hb1.map β).trans (by rw [List.map_cons, hks]; exact (hrest.cons s).trans hb2.symm)
    · exact h b' ⟨b', hb', by simp [hk']⟩
  · rintro ⟨h, hks⟩ b'' ⟨b', hb', hm⟩
    split at hm
    · rename_i hk'
      obtain rfl := only b' hb' (by simpa using hk')
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm
      · simp [hks]
      · split at hm
        · simp at hm
        · simp only [List.mem_singleton] at hm
          subst hm
          have := (hb1.map β).symm.trans ((h b' hb').trans hb2)
          rw [List.map_cons, hks] at this
          exact this.cons_inv
    · simp only [List.mem_singleton] at hm
      subst hm; exact h _ hb'

def inK (K : List Key) (b : Block) : List Key := b.1.filter (K.contains ·)
def outK (K : List Key) (b : Block) : List Key := b.1.filter (!K.contains ·)
def inN (N : List Name) (b : Block) : List Name := b.2.filter (N.contains ·)
def outN (N : List Name) (b : Block) : List Name := b.2.filter (!N.contains ·)

/-- The parts of a block one window fact `(K, N)` splits it into: its keys among `K` with its names among `N`, and the
rest; none if they cannot match. -/
def splitBy (K : List Key) (N : List Name) (b : Block) : Option (List Block) :=
  if (inK K b).length = (inN N b).length then some ([(inK K b, inN N b), (outK K b, outN N b)].filter (!·.1.isEmpty))
  else none

def refine1 (C : Cands) (c : List Key × List Name) : Option Cands :=
  (C.blocks.mapM (splitBy c.1 c.2)).map fun bss => ⟨bss.flatten⟩

/-- The blocks narrowed by every fact a window gave; none if they contradict the blocks. -/
def refineBy (C : Cands) (cs : Cons) : Option Cands := cs.foldlM refine1 C

end Cands

theorem forall2_mem_left {α γ : Type} {R : α → γ → Prop} : {xs : List α} → {ys : List γ} → Forall2 R xs ys →
    ∀ x ∈ xs, ∃ y ∈ ys, R x y
  | [], [], _, _, hx => absurd hx (by simp)
  | x :: xs, y :: ys, ⟨h, hs⟩, x', hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨y, by simp, h⟩
    · obtain ⟨y', hy', h'⟩ := forall2_mem_left hs x' hx; exact ⟨y', by simp [hy'], h'⟩
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

theorem forall2_mem_right {α γ : Type} {R : α → γ → Prop} : {xs : List α} → {ys : List γ} → Forall2 R xs ys →
    ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | [], [], _, _, hy => absurd hy (by simp)
  | x :: xs, y :: ys, ⟨h, hs⟩, y', hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨x, by simp, h⟩
    · obtain ⟨x', hx', h'⟩ := forall2_mem_right hs y' hy; exact ⟨x', by simp [hx'], h'⟩
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

theorem forall2_flatMap_perm {α γ δ : Type} {R : α → γ → Prop} {f : α → List δ} {g : γ → List δ}
    (hfg : ∀ a b, R a b → (g b).Perm (f a)) : {xs : List α} → {ys : List γ} → Forall2 R xs ys →
    (ys.flatMap g).Perm (xs.flatMap f)
  | [], [], _ => .refl _
  | _ :: _, _ :: _, ⟨h, hs⟩ => by
    simp only [List.flatMap_cons]; exact (hfg _ _ h).append (forall2_flatMap_perm hfg hs)
  | [], _ :: _, h | _ :: _, [], h => h.elim

namespace Cands

variable {C : Cands} {β : Key → Name}

theorem splitBy_spec {K : List Key} {N : List Name} {b : Block} {ps : List Block} (h : splitBy K N b = some ps)
    (hl : b.1.length = b.2.length) :
    (∀ p ∈ ps, p = (inK K b, inN N b) ∨ p = (outK K b, outN N b)) ∧
      ((inK K b, inN N b) ∈ ps ∨ inK K b = [] ∧ inN N b = []) ∧
      ((outK K b, outN N b) ∈ ps ∨ outK K b = [] ∧ outN N b = []) ∧
      (inK K b).length = (inN N b).length ∧ (outK K b).length = (outN N b).length := by
  unfold splitBy at h
  split at h
  · rename_i hin
    cases h
    have h1 := (List.filter_append_perm (K.contains ·) b.1).length_eq
    have h2 := (List.filter_append_perm (N.contains ·) b.2).length_eq
    rw [List.length_append] at h1 h2
    have hout : (outK K b).length = (outN N b).length := by
      simp only [inK, inN, outK, outN] at hin ⊢; omega
    refine ⟨fun p hp => ?_, ?_, ?_, hin, hout⟩
    · simp only [List.mem_filter, List.mem_cons, List.mem_nil_iff, or_false] at hp
      exact hp.1
    · by_cases he : inK K b = []
      · exact .inr ⟨he, List.eq_nil_of_length_eq_zero (by rw [← hin, he]; rfl)⟩
      · exact .inl (List.mem_filter.2 ⟨by simp, by simpa using he⟩)
    · by_cases he : outK K b = []
      · exact .inr ⟨he, List.eq_nil_of_length_eq_zero (by rw [← hout, he]; rfl)⟩
      · exact .inl (List.mem_filter.2 ⟨by simp, by simpa using he⟩)
  · cases h

theorem nodup_of_mem_flatMap {α γ : Type} {f : α → List γ} : {bs : List α} → (bs.flatMap f).Nodup →
    ∀ {b : α}, b ∈ bs → (f b).Nodup
  | [], _, _, hb => absurd hb (by simp)
  | c :: bs, h, b, hb => by
    rw [List.flatMap_cons, List.nodup_append] at h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h.1
    · exact nodup_of_mem_flatMap h.2.1 hb

theorem flatMap_flatten {α γ : Type} (f : α → List γ) : (xss : List (List α)) →
    xss.flatten.flatMap f = xss.flatMap fun xs => xs.flatMap f
  | [] => rfl
  | xs :: xss => by simp [List.flatMap_append, flatMap_flatten f xss]

theorem Ok.nodup_block (hC : C.Ok) {b : Block} (hb : b ∈ C.blocks) : b.1.Nodup ∧ b.2.Nodup :=
  ⟨nodup_of_mem_flatMap hC.keys hb, nodup_of_mem_flatMap hC.names hb⟩

theorem splitBy_flat {K : List Key} {N : List Name} {b : Block} {ps : List Block} (h : splitBy K N b = some ps)
    (hl : b.1.length = b.2.length) :
    ps.flatMap (·.1) = inK K b ++ outK K b ∧ ps.flatMap (·.2) = inN N b ++ outN N b := by
  obtain ⟨-, -, -, hin, hout⟩ := splitBy_spec h hl
  simp only [splitBy, hin, ↓reduceIte, Option.some.injEq] at h
  · subst h
    by_cases h1 : inK K b = [] <;> by_cases h2 : outK K b = []
    · have e1 := List.eq_nil_of_length_eq_zero (by rw [← hin, h1]; rfl : (inN N b).length = 0)
      have e2 := List.eq_nil_of_length_eq_zero (by rw [← hout, h2]; rfl : (outN N b).length = 0)
      simp [h1, h2, e1, e2]
    · have e1 := List.eq_nil_of_length_eq_zero (by rw [← hin, h1]; rfl : (inN N b).length = 0)
      simp [h1, h2, e1]
    · have e2 := List.eq_nil_of_length_eq_zero (by rw [← hout, h2]; rfl : (outN N b).length = 0)
      simp [h1, h2, e2]
    · simp [h1, h2]

/-- One window fact narrows the blocks exactly: the bindings left are those the blocks held possible that bind the
fact's keys to its names. -/
theorem refine1_has (hC : C.Ok) {K : List Key} {N : List Name} (hK : K.Nodup) (hN : N.Nodup) (hKs : K ⊆ C.keys)
    (hKN : K.length = N.length) {C' : Cands} (h : C.refine1 (K, N) = some C') :
    C'.Ok ∧ C'.keys.Perm C.keys ∧ C'.names.Perm C.names ∧ (C'.Has β ↔ C.Has β ∧ (K.map β).Perm N) := by
  unfold refine1 at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨bss, hm, rfl⟩ := h
  have hf := forall2_imp_mem (r' := fun b ps => splitBy K N b = some ps ∧ b ∈ C.blocks)
    (fun b hb _ _ h => ⟨h, hb⟩) (mapM_forall2 hm)
  have hkeys : (bss.flatten.flatMap (·.1)).Perm C.keys := by
    rw [flatMap_flatten]
    refine forall2_flatMap_perm (fun b ps ⟨h, hb⟩ => ?_) hf
    rw [(splitBy_flat h (hC.len b hb)).1]; exact List.filter_append_perm _ _
  have hnames : (bss.flatten.flatMap (·.2)).Perm C.names := by
    rw [flatMap_flatten]
    refine forall2_flatMap_perm (fun b ps ⟨h, hb⟩ => ?_) hf
    rw [(splitBy_flat h (hC.len b hb)).2]; exact List.filter_append_perm _ _
  have hmem : ∀ p, p ∈ bss.flatten ↔ ∃ b ∈ C.blocks, ∃ ps, splitBy K N b = some ps ∧ p ∈ ps := by
    intro p
    simp only [List.mem_flatten]
    constructor
    · rintro ⟨ps, hps, hp⟩
      obtain ⟨b, -, h, hb⟩ := forall2_mem_right hf ps hps
      exact ⟨b, hb, ps, h, hp⟩
    · rintro ⟨b, hb, ps, h, hp⟩
      obtain ⟨ps', hps', h', -⟩ := forall2_mem_left hf b hb
      rw [h] at h'; cases h'
      exact ⟨ps, hps', hp⟩
  have hsub : ∀ p ∈ bss.flatten, ∃ b ∈ C.blocks, p.1 ⊆ b.1 ∧ p.2 ⊆ b.2 ∧ p.1.length = p.2.length := by
    intro p hp
    obtain ⟨b, hb, ps, h, hp⟩ := (hmem p).1 hp
    obtain ⟨hps, -, -, hin, hout⟩ := splitBy_spec h (hC.len b hb)
    rcases hps p hp with rfl | rfl
    · exact ⟨b, hb, List.filter_sublist.subset, List.filter_sublist.subset, hin⟩
    · exact ⟨b, hb, List.filter_sublist.subset, List.filter_sublist.subset, hout⟩
  have hok : (⟨bss.flatten⟩ : Cands).Ok := by
    refine ⟨hkeys.nodup_iff.2 hC.keys, hnames.nodup_iff.2 hC.names, fun p hp => ?_, ?_⟩
    · obtain ⟨_, _, _, _, h⟩ := hsub p hp; exact h
    intro p hp k hk s hs
    obtain ⟨b, hb, h1, h2, -⟩ := hsub p hp
    exact hC.space b hb k (h1 hk) s (h2 hs)
  refine ⟨hok, hkeys, hnames, ?_⟩
  have hparts : Has β ⟨bss.flatten⟩ ↔
      ∀ b ∈ C.blocks, ((inK K b).map β).Perm (inN N b) ∧ ((outK K b).map β).Perm (outN N b) := by
    constructor
    · intro h b hb
      obtain ⟨ps, -, hs, -⟩ := forall2_mem_left hf b hb
      obtain ⟨-, hi, ho, -, -⟩ := splitBy_spec hs (hC.len b hb)
      have one : ∀ p, (p ∈ ps ∨ p.1 = [] ∧ p.2 = []) → (p.1.map β).Perm p.2 := by
        rintro p (hp | ⟨h1, h2⟩)
        · exact h p ((hmem p).2 ⟨b, hb, ps, hs, hp⟩)
        · rw [h1, h2]; exact .nil
      exact ⟨one _ hi, one _ ho⟩
    · intro h p hp
      obtain ⟨b, hb, ps, hs, hp⟩ := (hmem p).1 hp
      obtain ⟨hps, -, -, -, -⟩ := splitBy_spec hs (hC.len b hb)
      rcases hps p hp with rfl | rfl
      · exact (h b hb).1
      · exact (h b hb).2
  rw [hparts]
  constructor
  · intro h
    have hC' : C.Has β := fun b hb => by
      have := ((h b hb).1.append (h b hb).2)
      rw [← List.map_append] at this
      exact ((List.filter_append_perm _ _).map β).symm.trans (this.trans (List.filter_append_perm _ _))
    refine ⟨hC', perm_of_subset (nodup_map_of_inj hK fun a ha b hb => hC'.inj hC a (hKs ha) b (hKs hb)) ?_ ?_
      (by simp [hKN])⟩
    · exact hN
    · intro s hs
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hs
      obtain ⟨b, hb, hkb⟩ := List.mem_flatMap.1 (hKs hk)
      have : k ∈ inK K b := List.mem_filter.2 ⟨hkb, by simpa using hk⟩
      have h2 := (List.mem_filter.1 ((h b hb).1.mem_iff.1 (List.mem_map_of_mem this))).2
      simpa using h2
  · rintro ⟨hC', hp⟩ b hb
    obtain ⟨ps, -, hs, -⟩ := forall2_mem_left hf b hb
    obtain ⟨-, -, -, hin, hout⟩ := splitBy_spec hs (hC.len b hb)
    have hbk := (hC.nodup_block hb).1
    have hbn := (hC.nodup_block hb).2
    have inj : ∀ a ∈ C.keys, ∀ c ∈ C.keys, β a = β c → a = c := hC'.inj hC
    have hkb : ∀ k ∈ b.1, k ∈ C.keys := fun k hk => mem_keys hb hk
    constructor
    · refine perm_of_subset (nodup_map_of_inj (List.filter_sublist.nodup hbk)
        fun a ha c hc => inj a (hkb a (List.mem_filter.1 ha).1) c (hkb c (List.mem_filter.1 hc).1))
        (List.filter_sublist.nodup hbn) ?_ (by simp [hin])
      intro s hs
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hs
      obtain ⟨hk1, hk2⟩ := List.mem_filter.1 hk
      refine List.mem_filter.2 ⟨(hC' b hb).mem_iff.1 (List.mem_map_of_mem hk1), ?_⟩
      simpa using hp.mem_iff.1 (List.mem_map_of_mem (by simpa using hk2))
    · refine perm_of_subset (nodup_map_of_inj (List.filter_sublist.nodup hbk)
        fun a ha c hc => inj a (hkb a (List.mem_filter.1 ha).1) c (hkb c (List.mem_filter.1 hc).1))
        (List.filter_sublist.nodup hbn) ?_ (by simp [hout])
      intro s hs
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hs
      obtain ⟨hk1, hk2⟩ := List.mem_filter.1 hk
      refine List.mem_filter.2 ⟨(hC' b hb).mem_iff.1 (List.mem_map_of_mem hk1), ?_⟩
      simp only [Bool.not_eq_true'] at hk2 ⊢
      cases hc : N.contains (β k)
      · rfl
      · obtain ⟨k', hk', he⟩ := List.mem_map.1 (hp.mem_iff.2 (by simpa using hc))
        have := inj k' (hKs hk') k (hkb k hk1) he
        subst this
        simp [hk'] at hk2

/-- Every fact of a window narrows the blocks exactly. -/
theorem refineBy_has : (cs : Cons) → {C C' : Cands} → C.Ok →
    (∀ c ∈ cs, c.1.Nodup ∧ c.2.Nodup ∧ c.1 ⊆ C.keys ∧ c.1.length = c.2.length) → C.refineBy cs = some C' →
    C'.Ok ∧ C'.keys.Perm C.keys ∧ C'.names.Perm C.names ∧ (C'.Has β ↔ C.Has β ∧ ∀ c ∈ cs, (c.1.map β).Perm c.2)
  | [], C, C', hC, _, h => by
    simp only [refineBy, List.foldlM_nil, pure, Option.some.injEq] at h; subst h
    exact ⟨hC, .refl _, .refl _, by simp⟩
  | c :: cs, C, C', hC, hcs, h => by
    simp only [refineBy, List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨C1, h1, h2⟩ := h
    obtain ⟨hn1, hn2, hs, hl⟩ := hcs c (by simp)
    obtain ⟨hok1, hk1, hnm1, hhas1⟩ := refine1_has (β := β) hC hn1 hn2 hs hl h1
    obtain ⟨hok, hk, hnm, hhas⟩ := refineBy_has cs hok1 (fun c' hc' => by
      obtain ⟨a, b, c, d⟩ := hcs c' (by simp [hc'])
      exact ⟨a, b, fun k hk => hk1.symm.mem_iff.1 (c hk), d⟩) h2
    refine ⟨hok, hk.trans hk1, hnm.trans hnm1, ?_⟩
    rw [hhas, hhas1, List.forall_mem_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- The block holding a key, if any. -/
def blockOf (C : Cands) (k : Key) : Option Block := C.blocks.find? (·.1.contains k)

def blockOfName (C : Cands) (s : Name) : Option Block := C.blocks.find? (·.2.contains s)

/-- A key's skeleton label: its block's first key, the same for every key and name of the block. -/
def lab (C : Cands) (k : Key) : Option Key := (C.blockOf k).bind (·.1.head?)

def labName (C : Cands) (s : Name) : Option Key := (C.blockOfName s).bind (·.1.head?)

/-- Whether a label's block is undecided: two or more keys. -/
def undecided (C : Cands) : Option Key → Bool
  | some k => (C.blockOf k).any (2 ≤ ·.1.length)
  | none => false

theorem Ok.block_unique_name (hC : C.Ok) {b b' : Block} (hb : b ∈ C.blocks) (hb' : b' ∈ C.blocks) {s : Name}
    (hs : s ∈ b.2) (hs' : s ∈ b'.2) : b = b' :=
  mem_flatMap_unique hC.names hb hb' hs hs'

theorem blockOf_eq (hC : C.Ok) {b : Block} (hb : b ∈ C.blocks) {k : Key} (hk : k ∈ b.1) : C.blockOf k = some b := by
  unfold blockOf
  cases h : C.blocks.find? (·.1.contains k) with
  | none => exact absurd (List.find?_eq_none.1 h b hb) (by simpa using hk)
  | some b' =>
    have := List.find?_some h
    exact congrArg some (hC.block_unique (List.mem_of_find?_eq_some h) hb (by simpa using this) hk)

theorem blockOfName_eq (hC : C.Ok) {b : Block} (hb : b ∈ C.blocks) {s : Name} (hs : s ∈ b.2) :
    C.blockOfName s = some b := by
  unfold blockOfName
  cases h : C.blocks.find? (·.2.contains s) with
  | none => exact absurd (List.find?_eq_none.1 h b hb) (by simpa using hs)
  | some b' =>
    have := List.find?_some h
    exact congrArg some (hC.block_unique_name (List.mem_of_find?_eq_some h) hb (by simpa using this) hs)

theorem eq_single {α : Type} {l : List α} {a : α} (hl : l.length ≤ 1) (ha : a ∈ l) : l = [a] := by
  match l, hl, ha with
  | [b], _, ha => rw [List.mem_singleton.1 ha]

/-- A binding the blocks hold possible respects them, as `pairs_iff` needs. -/
theorem resp (hC : C.Ok) (h : C.Has β) : Resp C.lab C.labName C.undecided β (· ∈ C.keys) (· ∈ C.names) := by
  refine ⟨fun k hk => ?_, fun k s hk hs hl hu => ?_⟩
  · obtain ⟨b, hb, hkb⟩ := List.mem_flatMap.1 hk
    simp only [lab, labName, blockOf_eq hC hb hkb, blockOfName_eq hC hb ((h b hb).mem_iff.1 (List.mem_map_of_mem hkb))]
  · obtain ⟨b, hb, hkb⟩ := List.mem_flatMap.1 hk
    obtain ⟨b', hb', hsb⟩ := List.mem_flatMap.1 hs
    simp only [lab, labName, blockOf_eq hC hb hkb, blockOfName_eq hC hb' hsb, Option.bind_some] at hl hu
    obtain ⟨k0, hk0⟩ : ∃ k0, b.1.head? = some k0 := by
      cases e : b.1.head? with
      | none => simp at e; rw [e] at hkb; simp at hkb
      | some k0 => exact ⟨k0, rfl⟩
    rw [hk0] at hl hu
    have h0 : k0 ∈ b.1 := List.mem_of_mem_head? hk0
    have h0' : k0 ∈ b'.1 := List.mem_of_mem_head? hl.symm
    obtain rfl := hC.block_unique hb hb' h0 h0'
    simp only [undecided, blockOf_eq hC hb h0, Option.any_some, decide_eq_false_iff_not, Nat.not_le] at hu
    have e1 := eq_single (by omega) hkb
    have e2 := eq_single (by rw [← hC.len b hb]; omega) hsb
    have := h b hb
    rw [e1, e2] at this
    simpa using this

theorem parts_perm (hC : C.Ok) (h : C.Has β) {K : List Key} {N : List Name} (hKs : K ⊆ C.keys)
    (hp : (K.map β).Perm N) {b : Block} (hb : b ∈ C.blocks) :
    ((inK K b).map β).Perm (inN N b) ∧ ((outK K b).map β).Perm (outN N b) := by
  have inj := h.inj hC
  have hkb : ∀ k ∈ b.1, k ∈ C.keys := fun k hk => mem_keys hb hk
  have nd : ∀ {p : Key → Bool}, ((b.1.filter p).map β).Nodup := fun {p} =>
    nodup_map_of_inj (List.filter_sublist.nodup (hC.nodup_block hb).1)
      fun a ha c hc => inj a (hkb a (List.mem_filter.1 ha).1) c (hkb c (List.mem_filter.1 hc).1)
  have ndn : ∀ {p : Name → Bool}, (b.2.filter p).Nodup := fun {p} => List.filter_sublist.nodup (hC.nodup_block hb).2
  have back : ∀ s ∈ b.2, ∃ k ∈ b.1, β k = s := fun s hs => List.mem_map.1 ((h b hb).mem_iff.2 hs)
  have inK_iff : ∀ k ∈ b.1, (k ∈ K ↔ β k ∈ N) := fun k hk => ⟨fun hK => hp.mem_iff.1 (List.mem_map_of_mem hK),
    fun hN => by obtain ⟨k', hk', he⟩ := List.mem_map.1 (hp.mem_iff.2 hN); exact inj k' (hKs hk') k (hkb k hk) he ▸ hk'⟩
  refine ⟨(List.perm_ext_iff_of_nodup nd ndn).2 fun s => ⟨fun hs => ?_, fun hs => ?_⟩,
    (List.perm_ext_iff_of_nodup nd ndn).2 fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hs
    obtain ⟨hk1, hk2⟩ := List.mem_filter.1 hk
    exact List.mem_filter.2 ⟨(h b hb).mem_iff.1 (List.mem_map_of_mem hk1), by
      simpa using (inK_iff k hk1).1 (by simpa using hk2)⟩
  · obtain ⟨hs1, hs2⟩ := List.mem_filter.1 hs
    obtain ⟨k, hk, rfl⟩ := back s hs1
    exact List.mem_map_of_mem (List.mem_filter.2 ⟨hk, by simpa using (inK_iff k hk).2 (by simpa using hs2)⟩)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hs
    obtain ⟨hk1, hk2⟩ := List.mem_filter.1 hk
    refine List.mem_filter.2 ⟨(h b hb).mem_iff.1 (List.mem_map_of_mem hk1), ?_⟩
    have : ¬ k ∈ K := by simpa using hk2
    simpa [inK_iff k hk1] using this
  · obtain ⟨hs1, hs2⟩ := List.mem_filter.1 hs
    obtain ⟨k, hk, rfl⟩ := back s hs1
    have : ¬ β k ∈ N := by simpa using hs2
    exact List.mem_map_of_mem (List.mem_filter.2 ⟨hk, by simpa [inK_iff k hk] using this⟩)

theorem mapM_some {α γ : Type} {f : α → Option γ} : (xs : List α) → (∀ x ∈ xs, ∃ y, f x = some y) →
    ∃ ys, xs.mapM f = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := mapM_some xs fun x' hx' => h x' (by simp [hx'])
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys]⟩

/-- Where some binding the blocks hold possible meets every fact, narrowing by them succeeds. -/
theorem refineBy_some : (cs : Cons) → {C : Cands} → C.Ok →
    (∀ c ∈ cs, c.1.Nodup ∧ c.2.Nodup ∧ c.1 ⊆ C.keys ∧ c.1.length = c.2.length) → C.Has β →
    (∀ c ∈ cs, (c.1.map β).Perm c.2) → ∃ C', C.refineBy cs = some C'
  | [], C, _, _, _, _ => ⟨C, rfl⟩
  | c :: cs, C, hC, hcs, h, hp => by
    obtain ⟨hn1, hn2, hs, hl⟩ := hcs c (by simp)
    have hpc := hp c (by simp)
    obtain ⟨bss, hbss⟩ := mapM_some (f := splitBy c.1 c.2) C.blocks fun b hb => by
      have := parts_perm hC h hs hpc hb
      have hl' : (inK c.1 b).length = (inN c.2 b).length := by simpa using this.1.length_eq
      unfold splitBy; split
      · exact ⟨_, rfl⟩
      · contradiction
    have h1 : C.refine1 c = some ⟨bss.flatten⟩ := by simp only [refine1, hbss, Option.map_some]
    obtain ⟨hok1, hk1, -, hhas1⟩ := refine1_has (β := β) hC hn1 hn2 hs hl h1
    obtain ⟨C', h2⟩ := refineBy_some cs hok1 (fun c' hc' => by
      obtain ⟨a, b, c, d⟩ := hcs c' (by simp [hc'])
      exact ⟨a, b, fun k hk => hk1.symm.mem_iff.1 (c hk), d⟩) (hhas1.2 ⟨h, hpc⟩) fun c' hc' => hp c' (by simp [hc'])
    exact ⟨C', by simp only [refineBy, List.foldlM_cons, h1]; exact h2⟩

/-- What a window's trees do to the blocks. -/
inductive Narrowed where
  | done (C' : Cands)
  | differs
  /-- Items of the window tie undecided keys: decide `k` first, by each name of its block `b`. -/
  | decide (k : Key) (b : Block)

/-- The blocks narrowed by a window, whose spec trees are `es` and trace trees `ws`, all their keys and names in the
blocks. -/
def window (C : Cands) (es : List (Tree Key)) (ws : List (Tree Name)) : Narrowed :=
  if Tree.Same ((Tree.bag es).map C.lab) ((Tree.bag ws).map C.labName) then
    match pairs C.lab C.labName C.undecided (.bag es) (.bag ws) with
    | some cs => match C.refineBy cs with
      | some C' => .done C'
      | none => .differs
    | none => match (Tree.leavess es).find? (fun k => C.undecided (C.lab k)) with
      | some k => match C.blockOf k with
        | some b => if 2 ≤ b.1.length then .decide k b else .differs
        | none => .differs
      | none => .differs
  else .differs

theorem pairs_cons {es : List (Tree Key)} {ws : List (Tree Name)} {cs : Cons} (hes : ∀ k ∈ Tree.leavess es, k ∈ C.keys)
    (h : pairs C.lab C.labName C.undecided (.bag es) (.bag ws) = some cs) :
    ∀ c ∈ cs, c.1.Nodup ∧ c.2.Nodup ∧ c.1 ⊆ C.keys ∧ c.1.length = c.2.length := fun c hc => by
  obtain ⟨a, -, d, e, f⟩ := pairs_ok _ _ _ h c hc
  exact ⟨d, e, fun k hk => hes k (by simpa [Tree.leaves] using a hk), f⟩

/-- A window narrows the blocks exactly: the bindings left are those the blocks held possible under which the window's
trees are the trace's. -/
theorem window_done (hC : C.Ok) {es : List (Tree Key)} {ws : List (Tree Name)} (hes : ∀ k ∈ Tree.leavess es, k ∈ C.keys)
    (hws : ∀ s ∈ Tree.leavess ws, s ∈ C.names) {C' : Cands} (h : C.window es ws = .done C') :
    C'.Ok ∧ C'.keys.Perm C.keys ∧ C'.names.Perm C.names ∧
      (C'.Has β ↔ C.Has β ∧ Tree.Same ((Tree.bag es).map β) (Tree.bag ws)) := by
  unfold window at h
  split at h
  · rename_i hsk
    split at h
    · rename_i cs hcs
      split at h
      · rename_i C'' hC''
        cases h
        have hok := pairs_cons hes hcs
        obtain ⟨a, b, c, d⟩ := refineBy_has (β := β) cs hC hok hC''
        refine ⟨a, b, c, d.trans ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩⟩
        · exact (pairs_iff (resp hC h1) _ _ _ (by simpa [Tree.leaves] using hes) (by simpa [Tree.leaves] using hws)
            hsk hcs).2 h2
        · exact (pairs_iff (resp hC h1) _ _ _ (by simpa [Tree.leaves] using hes) (by simpa [Tree.leaves] using hws)
            hsk hcs).1 h2
      · cases h
    · split at h
      · split at h
        · split at h <;> cases h
        · cases h
      · cases h
  · cases h

/-- Where the blocks hold possible a binding under which the window's trees are the trace's, the window narrows to
blocks that keep it, or asks to decide a key of an undecided block. -/
theorem window_complete (hC : C.Ok) {es : List (Tree Key)} {ws : List (Tree Name)}
    (hes : ∀ k ∈ Tree.leavess es, k ∈ C.keys) (hws : ∀ s ∈ Tree.leavess ws, s ∈ C.names) (h : C.Has β)
    (hs : Tree.Same ((Tree.bag es).map β) (Tree.bag ws)) :
    (∃ C', C.window es ws = .done C' ∧ C'.Has β) ∨
      ∃ k b, C.window es ws = .decide k b ∧ b ∈ C.blocks ∧ k ∈ b.1 := by
  have hR := resp hC h
  have hsk := skel_of_same hR (x := .bag es) (by simpa [Tree.leaves] using hes) hs
  unfold window
  simp only [hsk, ↓reduceIte]
  split
  · rename_i cs hcs
    have hok := pairs_cons hes hcs
    have hp := (pairs_iff hR _ _ _ (by simpa [Tree.leaves] using hes) (by simpa [Tree.leaves] using hws) hsk hcs).1 hs
    obtain ⟨C', hC'⟩ := refineBy_some cs hC hok h hp
    rw [hC']
    exact .inl ⟨C', rfl, ((refineBy_has (β := β) cs hC hok hC').2.2.2).2 ⟨h, hp⟩⟩
  · rename_i hnone
    split
    · rename_i k hk
      have hku := List.find?_some hk
      have hkm := List.mem_of_find?_eq_some hk
      obtain ⟨b, hb, hkb⟩ := List.mem_flatMap.1 (hes k hkm)
      rw [blockOf_eq hC hb hkb]
      have h2 : 2 ≤ b.1.length := by
        obtain ⟨k0, hk0⟩ : ∃ k0, b.1.head? = some k0 := by
          cases e : b.1.head? with
          | none => simp at e; rw [e] at hkb; simp at hkb
          | some k0 => exact ⟨k0, rfl⟩
        simp only [lab, blockOf_eq hC hb hkb, Option.bind_some, hk0, undecided,
          blockOf_eq hC hb (List.mem_of_mem_head? hk0)] at hku
        simpa using hku
      simp only [h2, ↓reduceIte]
      exact .inr ⟨k, b, rfl, hb, hkb⟩
    · rename_i hfind
      exfalso
      obtain ⟨cs, hcs⟩ := pairs_some (und := C.undecided) (.bag es) (.bag ws) hsk fun k hk => by
        have := List.find?_eq_none.1 hfind k (by simpa [Tree.leaves] using hk)
        simpa using this
      rw [hcs] at hnone; cases hnone

theorem window_decide {es : List (Tree Key)} {ws : List (Tree Name)} {k : Key} {b : Block}
    (h : C.window es ws = .decide k b) : b ∈ C.blocks ∧ k ∈ b.1 ∧ 2 ≤ b.1.length := by
  unfold window at h
  split at h
  · split at h
    · split at h <;> cases h
    · split at h
      · split at h
        · rename_i b' hb
          split at h
          · rename_i h2
            cases h
            exact ⟨List.mem_of_find?_eq_some hb, by simpa using List.find?_some hb, h2⟩
          · cases h
        · cases h
      · cases h
  · cases h

/-- How undecided the blocks are: the keys of blocks with two or more. Deciding a key lowers it. -/
def weight (C : Cands) : Nat := (C.blocks.map fun b => if 2 ≤ b.1.length then b.1.length else 0).sum

theorem sum_le {α : Type} {f g : α → Nat} : (l : List α) → (∀ x ∈ l, g x ≤ f x) → (l.map g).sum ≤ (l.map f).sum
  | [], _ => by simp
  | y :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    have := h y (by simp); have := sum_le l fun x hx => h x (by simp [hx]); omega

theorem sum_lt {α : Type} {f g : α → Nat} : (l : List α) → (∀ x ∈ l, g x ≤ f x) → (∃ x ∈ l, g x < f x) →
    (l.map g).sum < (l.map f).sum
  | [], _, ⟨_, hx, _⟩ => absurd hx (by simp)
  | y :: l, hle, ⟨x, hx, hlt⟩ => by
    simp only [List.map_cons, List.sum_cons]
    by_cases hxy : x = y
    · subst hxy; have := sum_le l fun w hw => hle w (by simp [hw]); omega
    · have := sum_lt l (fun w hw => hle w (by simp [hw])) ⟨x, (List.mem_cons.1 hx).resolve_left hxy, hlt⟩
      have := hle y (by simp); omega

theorem sum_flatMap {α γ : Type} (T : α → List γ) (w : γ → Nat) : (l : List α) →
    ((l.flatMap T).map w).sum = (l.map fun b => ((T b).map w).sum).sum
  | [] => rfl
  | x :: l => by simp [List.flatMap_cons, List.sum_append, sum_flatMap T w l]

/-- Deciding a key of an undecided block lowers the weight. -/
theorem narrow_lt {b : Block} (hb : b ∈ C.blocks) {k : Key} {s : Name} (hk : k ∈ b.1)
    (h2 : 2 ≤ b.1.length) : (C.narrow k s).weight < C.weight := by
  let w : Block → Nat := fun b => if 2 ≤ b.1.length then b.1.length else 0
  let T : Block → List Block := fun b =>
    if b.1.contains k then ([k], [s]) :: if (b.1.erase k).isEmpty then [] else [(b.1.erase k, b.2.erase s)]
    else [b]
  have hT : ∀ x, ((T x).map w).sum ≤ w x ∧ (k ∈ x.1 → 2 ≤ x.1.length → ((T x).map w).sum < w x) := by
    intro x
    by_cases hx : k ∈ x.1
    · have hl := List.length_erase_of_mem hx
      have hpos : 1 ≤ x.1.length := List.length_pos_of_mem hx
      have hw1 : w ([k], [s]) = 0 := by simp [w]
      have hwr : w (x.1.erase k, x.2.erase s) ≤ x.1.length - 1 := by
        simp only [w, hl]; split <;> omega
      have hsum : ((T x).map w).sum ≤ x.1.length - 1 := by
        simp only [T, show x.1.contains k = true by simpa using hx, ↓reduceIte]
        split
        · simp [hw1]
        · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hw1]; omega
      have hwx : 2 ≤ x.1.length → w x = x.1.length := fun h => by simp [w, h]
      refine ⟨?_, fun _ h => by rw [hwx h]; omega⟩
      by_cases h : 2 ≤ x.1.length
      · rw [hwx h]; omega
      · have : x.1.length - 1 = 0 := by omega
        omega
    · simp only [T, show x.1.contains k = false by simpa using hx]
      exact ⟨by simp, fun h => absurd h hx⟩
  have e : (C.narrow k s).weight = (C.blocks.map fun b => ((T b).map w).sum).sum := by
    simp only [weight, narrow]; exact sum_flatMap T w C.blocks
  rw [e]
  exact sum_lt _ (fun x _ => (hT x).1) ⟨b, hb, (hT b).2 hk h2⟩

/-- Items without repeats, in order of their last appearance. -/
def nub {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ nub xs then nub xs else x :: nub xs

theorem mem_nub {α : Type} [DecidableEq α] {a : α} : {l : List α} → (a ∈ nub l ↔ a ∈ l)
  | [] => Iff.rfl
  | x :: xs => by
    unfold nub; split
    · rename_i h; rw [mem_nub]; constructor
      · exact fun ha => List.mem_cons_of_mem _ ha
      · intro ha; rcases List.mem_cons.1 ha with rfl | ha
        · exact mem_nub.1 h
        · exact ha
    · simp [mem_nub]

theorem nodup_nub {α : Type} [DecidableEq α] : (l : List α) → (nub l).Nodup
  | [] => .nil
  | x :: xs => by
    unfold nub; split
    · exact nodup_nub xs
    · rename_i h; exact List.nodup_cons.2 ⟨h, nodup_nub xs⟩

def newKeys (C : Cands) (ks : List Key) : List Key := nub (ks.filter (!C.keys.contains ·))

def newNames (C : Cands) (ns : List Name) : List Name := nub (ns.filter (!C.names.contains ·))

/-- The new keys and new names of one space. -/
def newPart (C : Cands) (ks : List Key) (ns : List Name) (w : Bool) : Block :=
  ((C.newKeys ks).filter (·.isWire == w), (C.newNames ns).filter (·.isWire == w))

/-- The blocks with a block of a window's new keys and new names for each space: keys the window shows that no block
holds, and names its trace lines hold that no block holds. None if the counts differ, as no one-to-one binding can then
read the window. -/
def addNew (C : Cands) (ks : List Key) (ns : List Name) : Option Cands :=
  if (C.newPart ks ns false).1.length = (C.newPart ks ns false).2.length ∧
      (C.newPart ks ns true).1.length = (C.newPart ks ns true).2.length then
    some ⟨C.blocks ++ [C.newPart ks ns false, C.newPart ks ns true].filter (!·.1.isEmpty)⟩
  else none

theorem nonempty_mem {p q x : Block} (h : x ∈ [p, q].filter (!·.1.isEmpty)) : x = p ∨ x = q := by
  simp only [List.mem_filter, List.mem_cons, List.mem_nil_iff, or_false] at h; exact h.1

theorem nonempty_has {p q : Block} (hp : p.1.length = p.2.length) (hq : q.1.length = q.2.length) :
    (∀ x ∈ [p, q].filter (!·.1.isEmpty), (x.1.map β).Perm x.2) ↔ (p.1.map β).Perm p.2 ∧ (q.1.map β).Perm q.2 := by
  have one : ∀ {x : Block}, x.1.length = x.2.length → x.1.isEmpty = true → (x.1.map β).Perm x.2 := fun hl he => by
    rw [List.isEmpty_iff.1 he] at hl ⊢; rw [List.eq_nil_of_length_eq_zero hl.symm]; exact .nil
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · cases he : p.1.isEmpty
      · exact h p (List.mem_filter.2 ⟨by simp, by simp [he]⟩)
      · exact one hp he
    · cases he : q.1.isEmpty
      · exact h q (List.mem_filter.2 ⟨by simp, by simp [he]⟩)
      · exact one hq he
  · rintro ⟨h1, h2⟩ x hx
    rcases nonempty_mem hx with rfl | rfl
    · exact h1
    · exact h2

theorem nonempty_flat {p q : Block} (hp : p.1.length = p.2.length) (hq : q.1.length = q.2.length) :
    ([p, q].filter (!·.1.isEmpty)).flatMap (·.1) = p.1 ++ q.1 ∧
      ([p, q].filter (!·.1.isEmpty)).flatMap (·.2) = p.2 ++ q.2 := by
  have e : ∀ {x : Block}, x.1.length = x.2.length → x.1.isEmpty = true → x.1 = [] ∧ x.2 = [] := fun hl he => by
    have := List.isEmpty_iff.1 he; rw [this] at hl; exact ⟨this, List.eq_nil_of_length_eq_zero hl.symm⟩
  cases h1 : p.1.isEmpty <;> cases h2 : q.1.isEmpty
  · simp [h1, h2]
  · obtain ⟨a, b⟩ := e hq h2; simp [h1, a, b]
  · obtain ⟨a, b⟩ := e hp h1; simp [h2, a, b]
  · obtain ⟨a, b⟩ := e hp h1; obtain ⟨c, d⟩ := e hq h2; simp [a, b, c, d]

theorem mem_newKeys {ks : List Key} {k : Key} : k ∈ C.newKeys ks ↔ k ∈ ks ∧ k ∉ C.keys := by
  simp [newKeys, mem_nub]

theorem mem_newNames {ns : List Name} {s : Name} : s ∈ C.newNames ns ↔ s ∈ ns ∧ s ∉ C.names := by
  simp [newNames, mem_nub]

theorem addNew_ok (hC : C.Ok) {ks : List Key} {ns : List Name} {C' : Cands} (h : C.addNew ks ns = some C') :
    C'.Ok ∧ (∀ b ∈ C.blocks, b ∈ C'.blocks) ∧ (∀ k, k ∈ C'.keys ↔ k ∈ C.keys ∨ k ∈ ks) ∧
      (∀ s, s ∈ C'.names ↔ s ∈ C.names ∨ s ∈ ns) ∧ (C'.Has β → C.Has β) := by
  unfold addNew at h
  split at h
  · rename_i hl
    cases h
    obtain ⟨fk, fn⟩ := nonempty_flat hl.1 hl.2
    have hkeys : Cands.keys ⟨C.blocks ++ [C.newPart ks ns false, C.newPart ks ns true].filter (!·.1.isEmpty)⟩ =
        C.keys ++ ((C.newPart ks ns false).1 ++ (C.newPart ks ns true).1) := by
      simp only [keys, List.flatMap_append, fk]
    have hnames : Cands.names ⟨C.blocks ++ [C.newPart ks ns false, C.newPart ks ns true].filter (!·.1.isEmpty)⟩ =
        C.names ++ ((C.newPart ks ns false).2 ++ (C.newPart ks ns true).2) := by
      simp only [names, List.flatMap_append, fn]
    have pk : ∀ {w k}, k ∈ (C.newPart ks ns w).1 ↔ k ∈ C.newKeys ks ∧ k.isWire = w := by simp [newPart]
    have pn : ∀ {w s}, s ∈ (C.newPart ks ns w).2 ↔ s ∈ C.newNames ns ∧ s.isWire = w := by simp [newPart]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, fun b hb => List.mem_append_left _ hb, fun k => ?_, fun s => ?_,
      fun h b hb => h b (List.mem_append_left _ hb)⟩
    · rw [hkeys, List.nodup_append, List.nodup_append]
      refine ⟨hC.keys, ⟨List.filter_sublist.nodup (nodup_nub _), List.filter_sublist.nodup (nodup_nub _), ?_⟩, ?_⟩
      · intro a ha b hb e; subst e; have := (pk.1 ha).2; have := (pk.1 hb).2; simp_all
      · intro a ha b hb e; subst e
        rcases List.mem_append.1 hb with hb | hb <;> exact (mem_newKeys.1 (pk.1 hb).1).2 ha
    · rw [hnames, List.nodup_append, List.nodup_append]
      refine ⟨hC.names, ⟨List.filter_sublist.nodup (nodup_nub _), List.filter_sublist.nodup (nodup_nub _), ?_⟩, ?_⟩
      · intro a ha b hb e; subst e; have := (pn.1 ha).2; have := (pn.1 hb).2; simp_all
      · intro a ha b hb e; subst e
        rcases List.mem_append.1 hb with hb | hb <;> exact (mem_newNames.1 (pn.1 hb).1).2 ha
    · intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact hC.len b hb
      · rcases nonempty_mem hb with rfl | rfl
        · exact hl.1
        · exact hl.2
    · intro b hb k hk s hs
      rcases List.mem_append.1 hb with hb | hb
      · exact hC.space b hb k hk s hs
      · rcases nonempty_mem hb with rfl | rfl
        · rw [(pk.1 hk).2, (pn.1 hs).2]
        · rw [(pk.1 hk).2, (pn.1 hs).2]
    · rw [hkeys]
      simp only [List.mem_append, pk, mem_newKeys]
      constructor
      · rintro (h | ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩) <;> simp [h]
      · rintro (h | h)
        · exact .inl h
        · by_cases hc : k ∈ C.keys
          · exact .inl hc
          · cases k.isWire <;> simp [h, hc]
    · rw [hnames]
      simp only [List.mem_append, pn, mem_newNames]
      constructor
      · rintro (h | ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩) <;> simp [h]
      · rintro (h | h)
        · exact .inl h
        · by_cases hc : s ∈ C.names
          · exact .inl hc
          · cases s.isWire <;> simp [h, hc]
  · cases h

/-- Where a binding the blocks hold possible binds the window's new keys one to one onto its new names, space by space,
the new blocks hold it possible. -/
theorem addNew_complete (h : C.Has β) {ks : List Key} {ns : List Name}
    (hinj : ∀ a ∈ C.keys ++ ks, ∀ b ∈ C.keys ++ ks, β a = β b → a = b) (hks : ∀ k ∈ ks, β k ∈ ns)
    (hns : ∀ s ∈ ns, ∃ k ∈ C.keys ++ ks, β k = s) (hw : ∀ k ∈ ks, (β k).isWire = k.isWire) :
    ∃ C', C.addNew ks ns = some C' ∧ C'.Has β := by
  have part : ∀ w, ((C.newPart ks ns w).1.map β).Perm (C.newPart ks ns w).2 := by
    intro w
    refine (List.perm_ext_iff_of_nodup (nodup_map_of_inj (List.filter_sublist.nodup (nodup_nub _))
      fun a ha b hb => hinj a ?_ b ?_) (List.filter_sublist.nodup (nodup_nub _))).2 fun s => ⟨fun hs => ?_, fun hs => ?_⟩
    · exact List.mem_append_right _ (mem_newKeys.1 (List.mem_filter.1 ha).1).1
    · exact List.mem_append_right _ (mem_newKeys.1 (List.mem_filter.1 hb).1).1
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hs
      obtain ⟨hk1, hk2⟩ := List.mem_filter.1 hk
      obtain ⟨hk3, hk4⟩ := mem_newKeys.1 hk1
      refine List.mem_filter.2 ⟨mem_newNames.2 ⟨hks k hk3, fun hn => hk4 ?_⟩, by rw [hw k hk3]; exact hk2⟩
      obtain ⟨k', hk', he⟩ := List.mem_map.1 (h.perm.mem_iff.2 hn)
      exact hinj k' (List.mem_append_left _ hk') k (List.mem_append_right _ hk3) he ▸ hk'
    · obtain ⟨hs1, hs2⟩ := List.mem_filter.1 hs
      obtain ⟨hs3, hs4⟩ := mem_newNames.1 hs1
      obtain ⟨k, hk, rfl⟩ := hns s hs3
      have hkC : k ∉ C.keys := fun hc => hs4 (h.mem hc)
      have hks' : k ∈ ks := (List.mem_append.1 hk).resolve_left hkC
      refine List.mem_map_of_mem (List.mem_filter.2 ⟨mem_newKeys.2 ⟨hks', hkC⟩, ?_⟩)
      rw [← hw k hks']; exact hs2
  have hl : ∀ w, (C.newPart ks ns w).1.length = (C.newPart ks ns w).2.length := fun w => by
    simpa using (part w).length_eq
  refine ⟨⟨C.blocks ++ [C.newPart ks ns false, C.newPart ks ns true].filter (!·.1.isEmpty)⟩,
    by unfold addNew; simp only [hl false, hl true, and_self, ↓reduceIte], fun b hb => ?_⟩
  rcases List.mem_append.1 hb with hb | hb
  · exact h b hb
  · exact (nonempty_has (hl false) (hl true)).2 ⟨part false, part true⟩ b hb

theorem flatMap_perm {α γ : Type} {f g : α → List γ} : (l : List α) → (∀ x ∈ l, (f x).Perm (g x)) →
    (l.flatMap f).Perm (l.flatMap g)
  | [], _ => .refl _
  | x :: l, h => by
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (flatMap_perm l fun y hy => h y (by simp [hy]))

/-- Deciding a key keeps the keys and names, and the blocks' form. -/
theorem narrow_ok (hC : C.Ok) {b : Block} (hb : b ∈ C.blocks) {k : Key} {s : Name} (hk : k ∈ b.1) (hs : s ∈ b.2) :
    (C.narrow k s).Ok ∧ (C.narrow k s).keys.Perm C.keys ∧ (C.narrow k s).names.Perm C.names := by
  have only : ∀ b' ∈ C.blocks, k ∈ b'.1 → b' = b := fun b' hb' hk' => hC.block_unique hb' hb hk' hk
  have hb1 : b.1.Perm (k :: b.1.erase k) := List.perm_cons_erase hk
  have hb2 : b.2.Perm (s :: b.2.erase s) := List.perm_cons_erase hs
  have hl := hC.len b hb
  have hle : (b.1.erase k).length = (b.2.erase s).length := by
    rw [List.length_erase_of_mem hk, List.length_erase_of_mem hs, hl]
  have T : ∀ b' ∈ C.blocks, ∀ p ∈ (if b'.1.contains k then ([k], [s]) ::
      if (b'.1.erase k).isEmpty then [] else [(b'.1.erase k, b'.2.erase s)] else [b']),
      p.1 ⊆ b'.1 ∧ p.2 ⊆ b'.2 ∧ p.1.length = p.2.length := by
    intro b' hb' p hp
    split at hp
    · obtain rfl := only b' hb' (by simpa using ‹b'.1.contains k = true›)
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨by simp [hk], by simp [hs], rfl⟩
      · split at hp
        · simp at hp
        · simp only [List.mem_singleton] at hp; subst hp
          exact ⟨List.erase_subset, List.erase_subset, hle⟩
    · simp only [List.mem_singleton] at hp; subst hp
      exact ⟨fun _ h => h, fun _ h => h, hC.len p hb'⟩
  have flat : ∀ b' ∈ C.blocks, ((if b'.1.contains k then ([k], [s]) ::
      if (b'.1.erase k).isEmpty then [] else [(b'.1.erase k, b'.2.erase s)] else [b']).flatMap (·.1)).Perm b'.1 ∧
      ((if b'.1.contains k then ([k], [s]) ::
      if (b'.1.erase k).isEmpty then [] else [(b'.1.erase k, b'.2.erase s)] else [b']).flatMap (·.2)).Perm b'.2 := by
    intro b' hb'
    split
    · rename_i hc
      obtain rfl := only b' hb' (by simpa using hc)
      split
      · rename_i he
        have e1 : b'.1.erase k = [] := List.isEmpty_iff.1 he
        have e2 : b'.2.erase s = [] := List.eq_nil_of_length_eq_zero (by rw [← hle, e1]; rfl)
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact ⟨by rw [← e1]; exact hb1.symm, by rw [← e2]; exact hb2.symm⟩
      · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.singleton_append]
        exact ⟨hb1.symm, hb2.symm⟩
    · simp
  have hkeys : (C.narrow k s).keys.Perm C.keys := by
    simp only [keys, narrow, List.flatMap_assoc]; exact flatMap_perm _ fun b' hb' => (flat b' hb').1
  have hnames : (C.narrow k s).names.Perm C.names := by
    simp only [names, narrow, List.flatMap_assoc]; exact flatMap_perm _ fun b' hb' => (flat b' hb').2
  refine ⟨⟨hkeys.nodup_iff.2 hC.keys, hnames.nodup_iff.2 hC.names, fun p hp => ?_, fun p hp => ?_⟩, hkeys, hnames⟩
  · simp only [narrow, List.mem_flatMap] at hp
    obtain ⟨b', hb', hp⟩ := hp
    exact (T b' hb' p hp).2.2
  · simp only [narrow, List.mem_flatMap] at hp
    obtain ⟨b', hb', hp⟩ := hp
    obtain ⟨h1, h2, -⟩ := T b' hb' p hp
    exact fun k' hk' s' hs' => hC.space b' hb' k' (h1 hk') s' (h2 hs')

theorem flatMap_eq {α γ : Type} {f g : α → List γ} : (l : List α) → (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by simp only [List.flatMap_cons, h x (by simp), flatMap_eq l fun y hy => h y (by simp [hy])]

theorem lookup_of_mem {α γ : Type} [BEq α] [LawfulBEq α] : {L : List (α × γ)} → (L.map Prod.fst).Nodup →
    ∀ {a : α} {c : γ}, (a, c) ∈ L → L.lookup a = some c
  | [], _, _, _, h => absurd h (by simp)
  | (a', c') :: L, hn, a, c, h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.1 h with e | h
    · cases e; simp
    · have : a ≠ a' := fun e => hn.1 ⟨(a, c), h, e⟩
      simp only [List.lookup_cons, beq_eq_false_iff_ne.2 this]
      exact lookup_of_mem hn.2 h

theorem map_fst_zip {α γ : Type} : (as : List α) → (cs : List γ) → as.length = cs.length →
    (as.zip cs).map Prod.fst = as ∧ (as.zip cs).map Prod.snd = cs
  | [], [], _ => ⟨rfl, rfl⟩
  | a :: as, c :: cs, h => by
    obtain ⟨h1, h2⟩ := map_fst_zip as cs (by simpa using h); simp [h1, h2]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

-- A key outside every block is never read.
set_option linter.tazuna.silentDefault false in
/-- Blocks in form hold some binding possible: each block's keys to its names in order. -/
theorem Ok.exists_has (hC : C.Ok) : ∃ β : Key → Name, C.Has β := by
  let L := C.blocks.flatMap fun b => b.1.zip b.2
  have hL : L.map Prod.fst = C.keys := by
    simp only [L, List.map_flatMap]
    exact flatMap_eq _ fun b hb => (map_fst_zip b.1 b.2 (hC.len b hb)).1
  refine ⟨fun k => (L.lookup k).getD default, fun b hb => ?_⟩
  obtain ⟨h1, h2⟩ := map_fst_zip b.1 b.2 (hC.len b hb)
  have : b.1.map (fun k => (L.lookup k).getD default) = (b.1.zip b.2).map Prod.snd := by
    conv => lhs; rw [← h1]
    rw [List.map_map]
    refine List.map_congr_left fun p hp => ?_
    have hpL : p ∈ L := List.mem_flatMap.2 ⟨b, hb, hp⟩
    simp only [Function.comp, lookup_of_mem (hL ▸ hC.keys) (show (p.1, p.2) ∈ L from hpL), Option.getD_some]
  rw [this, h2]

end Cands

end Tazuna.Trace
