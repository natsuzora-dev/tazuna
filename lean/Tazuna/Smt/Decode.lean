import Tazuna.Smt.EncodeThm

/-! T3, decoding: the value of a first-order type that an SMT value codes, as `RelV` relates them, and the embedding
of a value as the SMT value that codes it. `decode_rel` proves that a decoded value is the one the model's value
codes, so a value read from a model is a real value of its type; `decode_embed` proves that decoding inverts the
embedding, so every value within the layout's slots is some model's value. A bag or table embeds its items in its
first slots, in order, and decodes from its occupied slots, in order; a value with more items than its slots has no
embedding, and a table whose occupied slots repeat a key has no decoding. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout)

/-- The slots of a collection's value: each slot's flag and its `w` item values. -/
def slotsView (dt w : Nat) : List Val → Option (List (Bool × List Val))
  | [] => some []
  | .ctor d k (.bool b :: vs) :: rest =>
    if d = dt ∧ k = 0 ∧ vs.length = w then (slotsView dt w rest).map ((b, vs) :: ·) else none
  | _ :: _ => none

/-- The `n` slots of a collection value of datatype `d` whose slots are datatype `dt`. -/
def collView (d dt n w : Nat) : Val → Option (List (Bool × List Val))
  | .ctor d' k vals => if d' = d ∧ k = 0 then (slotsView dt w vals).bind fun sv =>
      if sv.length = n then some sv else none else none
  | _ => none

/-- A table value from entries whose keys differ by `f`, or none when two share a key. -/
def uniqueKeys {κ ν : Type} (f : κ → κ → Bool) (xs : List (κ × ν)) : Option { xs : List (κ × ν) // KeysUnique f xs } :=
  if h : xs.Pairwise (fun (a b : κ × ν) => f a.1 b.1 = false ∧ f b.1 a.1 = false) then some ⟨xs, h⟩ else none

/-- The id an id's constructor and fields code: a fresh one by its number, an outside one by its name. -/
def decodeId : Nat → List Val → Option IdV
  | 0, [.int n] => if 0 ≤ n then some (.fresh n.toNat) else none
  | 1, [.str s] => some (.named s)
  | _, _ => none

mutual
/-- The value an SMT value codes. -/
def decodeV : (t : Ty) → Val → Option t.den
  | .int, .int n => some n
  | .str, .str s => some s
  | .date, .int n => some n
  | .id, .ctor d' k args => match L.find? .id with
    | some (d, _) => if d' = d then decodeId k args else none
    | none => none
  | .adt 0 _ [[], []], .bool b => some (if b then .inl () else .inr (.inl ()))
  | .adt (i + 1) a vs, v => match L.find? (.adt (i + 1) a vs) with
    | some (d, _) => decodeAlts d 0 vs v
    | none => none
  | .tuple ts, .ctor d' k vals => match L.find? (.tuple ts) with
    | some (d, _) => if d' = d ∧ k = 0 then decodeVs ts vals else none
    | none => none
  | .bag t, v => match L.find? (.bag t), L.find? (.tuple [Ty.bool, t]) with
    | some (d, n), some (dt, _) => (collView d dt n 1 v).bind fun sv =>
      (occupied sv).mapM fun
        | [z] => decodeV t z
        | _ => none
    | _, _ => none
  | .table k w, v => match L.find? (.table k w), L.find? (.tuple [Ty.bool, k, w]) with
    | some (d, n), some (dt, _) => (collView d dt n 2 v).bind fun sv =>
      ((occupied sv).mapM fun
        | [zk, zv] => (decodeV k zk).bind fun a => (decodeV w zv).map fun b => (a, b)
        | _ => none).bind (uniqueKeys (Ty.semWith Dsl.val k).2)
    | _, _ => none
  | _, _ => none
def decodeVs : (ts : List Ty) → List Val → Option (Ty.dens ts)
  | [], [] => some ()
  | t :: ts, v :: vs => (decodeV t v).bind fun a => (decodeVs ts vs).map fun b => (a, b)
  | _, _ => none
def decodeAlts (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Val → Option (Ty.alts vs)
  | _, [], _ => none
  | k, fs :: vs, v => match v with
    | .ctor d' k' vals => if d' = d ∧ k' = k then (decodeVs fs vals).map .inl else (decodeAlts d (k + 1) vs v).map .inr
    | _ => none
end

/-- The slots of a collection holding the item values `zs` first, then free slots up to `n`; none when the items
outnumber the slots. -/
def fillSlots (n w : Nat) (zs : List (List Val)) : Option (List (Bool × List Val)) :=
  if zs.length ≤ n then some (zs.map (true, ·) ++ List.replicate (n - zs.length) (false, List.replicate w (.bool false)))
  else none

mutual
/-- The SMT value that codes a value, as `RelV` relates them. -/
def embedV : (t : Ty) → t.den → Option Val
  | .int, n => some (.int n)
  | .str, s => some (.str s)
  | .date, n => some (.int n)
  | .id, x => (L.find? .id).map fun (d, _) => idVal d x
  | .adt 0 _ [[], []], x => some (.bool (altsBool x))
  | .adt (i + 1) a vs, x => match L.find? (.adt (i + 1) a vs) with
    | some (d, _) => embedAlts d 0 vs x
    | none => none
  | .tuple ts, x => match L.find? (.tuple ts) with
    | some (d, _) => (embedVs ts x).map (.ctor d 0)
    | none => none
  | .bag t, xs => match L.find? (.bag t), L.find? (.tuple [Ty.bool, t]) with
    | some (d, n), some (dt, _) =>
      ((xs.mapM fun x => (embedV t x).map ([·])).bind (fillSlots n 1)).map (slotsVal d dt)
    | _, _ => none
  | .table k w, x => match L.find? (.table k w), L.find? (.tuple [Ty.bool, k, w]) with
    | some (d, n), some (dt, _) =>
      ((x.1.mapM fun e => (embedV k e.1).bind fun a => (embedV w e.2).map fun b => [a, b]).bind
        (fillSlots n 2)).map (slotsVal d dt)
    | _, _ => none
  | _, _ => none
def embedVs : (ts : List Ty) → Ty.dens ts → Option (List Val)
  | [], _ => some []
  | t :: ts, (x, xs) => (embedV t x).bind fun a => (embedVs ts xs).map (a :: ·)
def embedAlts (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Ty.alts vs → Option Val
  | k, fs :: _, .inl x => (embedVs fs x).map (.ctor d k)
  | k, _ :: vs, .inr y => embedAlts d (k + 1) vs y
end

end

section
variable {L : Layout}

theorem slotsView_eq {dt w : Nat} : {vals : List Val} → {sv : List (Bool × List Val)} → slotsView dt w vals = some sv →
    vals = sv.map (fun (b, vs) => .ctor dt 0 (.bool b :: vs)) ∧ ∀ p ∈ sv, p.2.length = w
  | [], sv, h => by simp only [slotsView, Option.some.injEq] at h; subst h; simp
  | .ctor d k (.bool b :: vs) :: rest, sv, h => by
    simp only [slotsView] at h
    split at h
    · rename_i hc
      obtain ⟨sv', h', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨h1, h2⟩ := slotsView_eq h'
      obtain ⟨rfl, rfl, hl⟩ := hc
      refine ⟨by simp [h1], ?_⟩
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hl
      · exact h2 p hp
    · cases h
  | .int _ :: _, _, h | .bool _ :: _, _, h | .str _ :: _, _, h | .ctor _ _ [] :: _, _, h
  | .ctor _ _ (.int _ :: _) :: _, _, h | .ctor _ _ (.str _ :: _) :: _, _, h
  | .ctor _ _ (.ctor .. :: _) :: _, _, h => by simp [slotsView] at h

theorem collView_eq {d dt n w : Nat} {v : Val} {sv : List (Bool × List Val)} (h : collView d dt n w v = some sv) :
    v = slotsVal d dt sv ∧ sv.length = n ∧ ∀ p ∈ sv, p.2.length = w := by
  unfold collView at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨sv', h1, h2⟩ := Option.bind_eq_some_iff.1 h
      split at h2
      · cases h2
        obtain ⟨rfl, rfl⟩ := hc
        obtain ⟨hv, hw⟩ := slotsView_eq h1
        exact ⟨by simp [slotsVal, hv], by assumption, hw⟩
      · cases h2
    · cases h
  · cases h

theorem slotsView_map {dt w : Nat} : (sv : List (Bool × List Val)) → (∀ p ∈ sv, p.2.length = w) →
    slotsView dt w (sv.map fun (b, vs) => .ctor dt 0 (.bool b :: vs)) = some sv
  | [], _ => rfl
  | (b, vs) :: sv, hw => by
    have hl : vs.length = w := hw (b, vs) (by simp)
    simp only [List.map_cons, slotsView, hl, and_self, ite_true]
    rw [slotsView_map sv (fun p hp => hw p (by simp [hp]))]; rfl

theorem collView_slots {d dt w : Nat} (sv : List (Bool × List Val)) (hw : ∀ p ∈ sv, p.2.length = w) :
    collView d dt sv.length w (slotsVal d dt sv) = some sv := by
  simp [collView, slotsVal, slotsView_map sv hw]

theorem mapM_forall2 {α β : Type} {E : α → β → Prop} {f : β → Option α} (hf : ∀ b a, f b = some a → E a b) :
    (bs : List β) → (as : List α) → bs.mapM f = some as → Forall2 E as bs
  | [], as, h => by simp only [List.mapM_nil] at h; cases h; trivial
  | b :: bs, as, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, ha, as', has, rfl⟩ := h
    exact ⟨hf b a ha, mapM_forall2 hf bs as' has⟩

theorem occupied_fill (n w : Nat) (zs : List (List Val)) (sv : List (Bool × List Val)) (h : fillSlots n w zs = some sv) :
    occupied sv = zs ∧ sv.length = n := by
  unfold fillSlots at h
  split at h
  · cases h
    refine ⟨?_, by simp; omega⟩
    simp [occupied, List.filterMap_append, Function.comp_def]
  · cases h

theorem fill_width {n w : Nat} {zs : List (List Val)} {sv : List (Bool × List Val)} (hz : ∀ z ∈ zs, z.length = w)
    (h : fillSlots n w zs = some sv) : ∀ p ∈ sv, p.2.length = w := by
  unfold fillSlots at h
  split at h
  · cases h
    intro p hp
    simp only [List.mem_append, List.mem_map, List.mem_replicate] at hp
    rcases hp with ⟨z, hz', rfl⟩ | ⟨_, rfl⟩
    · exact hz z hz'
    · simp
  · cases h

theorem bind_some {α β : Type} {o : Option α} {f : α → Option β} {b : β} :
    o.bind f = some b ↔ ∃ a, o = some a ∧ f a = some b := Option.bind_eq_some_iff

theorem map_some {α β : Type} {o : Option α} {f : α → β} {b : β} :
    o.map f = some b ↔ ∃ a, o = some a ∧ f a = b := Option.map_eq_some_iff

theorem decodeId_val (d : Nat) {k : Nat} {args : List Val} {x : IdV} (h : decodeId k args = some x) :
    Val.ctor d k args = idVal d x := by
  unfold decodeId at h
  split at h
  · split at h
    · cases h; simp [idVal]; omega
    · cases h
  · cases h; rfl
  · cases h

mutual
/-- T3: a decoded value is the value the SMT value codes. -/
theorem decode_rel : (t : Ty) → (v : Val) → (x : t.den) → decodeV L t v = some x → RelV L t x v
  | .int, .int n, x, h | .date, .int n, x, h => by cases h; rfl
  | .str, .str s, x, h => by cases h; rfl
  | .id, .ctor d' k args, x, h => by
    simp only [decodeV] at h
    split at h
    · rename_i d n hf
      by_cases hd : d' = d
      · subst hd; simp only at h; exact ⟨d', n, hf, decodeId_val d' h⟩
      · simp [hd] at h
    · cases h
  | .adt 0 _ [[], []], .bool b, x, h => by
    cases h; exact ⟨rfl, by cases b <;> rfl⟩
  | .adt (i + 1) a vs, v, x, h => by
    simp only [decodeV] at h
    split at h
    · rename_i d n hf; exact ⟨d, n, hf, decodeAlts_rel d 0 vs v x h⟩
    · cases h
  | .tuple ts, .ctor d' k vals, x, h => by
    simp only [decodeV] at h
    split at h
    · rename_i d n hf
      by_cases hc : d' = d ∧ k = 0
      · obtain ⟨rfl, rfl⟩ := hc
        simp only [and_self] at h
        exact ⟨d', n, vals, hf, rfl, decodeVs_rel ts vals x h⟩
      · simp [hc] at h
    · cases h
  | .bag t, v, x, h => by
    simp only [decodeV] at h
    split at h
    · rename_i d n dt m hf hft
      obtain ⟨sv, hsv, h⟩ := bind_some.1 h
      obtain ⟨hv, hn, hw⟩ := collView_eq hsv
      refine ⟨d, n, dt, m, sv, hf, hft, hn, hv, hw, x, List.Perm.refl _, ?_⟩
      refine mapM_forall2 (fun b a hb => ?_) _ _ h
      match b, hb with
      | [z], hb => exact ⟨z, rfl, decode_rel t z a hb⟩
    · cases h
  | .table k w, v, x, h => by
    simp only [decodeV] at h
    split at h
    · rename_i d n dt m hf hft
      obtain ⟨sv, hsv, h⟩ := bind_some.1 h
      obtain ⟨xs, hxs, h⟩ := bind_some.1 h
      obtain ⟨hv, hn, hw⟩ := collView_eq hsv
      unfold uniqueKeys at h
      split at h
      · cases h
        refine ⟨d, n, dt, m, sv, hf, hft, hn, hv, hw, xs, List.Perm.refl _, ?_⟩
        refine mapM_forall2 (fun b a hb => ?_) _ _ hxs
        match b, hb with
        | [zk, zv], hb =>
          obtain ⟨y1, h1, h⟩ := bind_some.1 hb
          obtain ⟨y2, h2, rfl⟩ := map_some.1 h
          exact ⟨zk, zv, rfl, decode_rel k zk y1 h1, decode_rel w zv y2 h2⟩
      · cases h
    · cases h
theorem decodeVs_rel : (ts : List Ty) → (vals : List Val) → (x : Ty.dens ts) → decodeVs L ts vals = some x →
    RelVs L ts x vals
  | [], [], _, _ => rfl
  | t :: ts, v :: vs, x, h => by
    obtain ⟨y, hy, h⟩ := bind_some.1 h
    obtain ⟨ys, hys, rfl⟩ := map_some.1 h
    exact ⟨v, vs, rfl, decode_rel t v y hy, decodeVs_rel ts vs ys hys⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [decodeVs] at h
theorem decodeAlts_rel (d : Nat) : (k : Nat) → (vs : List (List Ty)) → (v : Val) → (x : Ty.alts vs) →
    decodeAlts L d k vs v = some x → RelAlts L d k vs x v
  | _, [], _, _, h => by simp [decodeAlts] at h
  | k, fs :: vs, .ctor d' k' vals, x, h => by
    simp only [decodeAlts] at h
    split at h
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨y, hy, rfl⟩ := map_some.1 h
      exact ⟨vals, rfl, decodeVs_rel fs vals y hy⟩
    · obtain ⟨y, hy, rfl⟩ := map_some.1 h
      exact decodeAlts_rel d (k + 1) vs _ y hy
  | _, _ :: _, .int _, _, h | _, _ :: _, .bool _, _, h | _, _ :: _, .str _, _, h => by simp [decodeAlts] at h
end

theorem mapM_inverse {α β : Type} {f : α → Option β} {g : β → Option α} (hfg : ∀ a b, f a = some b → g b = some a) :
    (as : List α) → (bs : List β) → as.mapM f = some bs → bs.mapM g = some as
  | [], bs, h => by simp only [List.mapM_nil] at h; cases h; rfl
  | a :: as, bs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs', hbs, rfl⟩ := h
    simp [hfg a b hb, mapM_inverse hfg as bs' hbs]

theorem mapM_lengths {α : Type} {f : α → Option (List Val)} {w : Nat} (hf : ∀ a z, f a = some z → z.length = w) :
    (as : List α) → (zs : List (List Val)) → as.mapM f = some zs → ∀ z ∈ zs, z.length = w
  | [], zs, h => by simp only [List.mapM_nil] at h; cases h; simp
  | a :: as, zs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs', hbs, rfl⟩ := h
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hf a z hb
    · exact mapM_lengths hf as bs' hbs z hz

mutual
/-- T3: decoding inverts the embedding. -/
theorem decode_embed : (t : Ty) → (x : t.den) → (v : Val) → embedV L t x = some v → decodeV L t v = some x
  | .int, x, v, h | .date, x, v, h => by cases h; rfl
  | .str, x, v, h => by cases h; rfl
  | .id, x, v, h => by
    obtain ⟨⟨d, n⟩, hf, rfl⟩ := map_some.1 h
    cases x <;> simp [idVal, decodeV, hf, decodeId] <;> rfl
  | .adt 0 _ [[], []], x, v, h => by
    cases h
    match x with
    | .inl () => rfl
    | .inr (.inl ()) => rfl
  | .adt (i + 1) a vs, x, v, h => by
    simp only [embedV] at h
    split at h
    · rename_i d n hf
      simp only [decodeV, hf]
      exact decodeAlts_embed d 0 vs x v h
    · cases h
  | .tuple ts, x, v, h => by
    simp only [embedV] at h
    split at h
    · rename_i d n hf
      obtain ⟨vals, hv, rfl⟩ := map_some.1 h
      simp [decodeV, hf, decodeVs_embed ts x vals hv]; rfl
    · cases h
  | .bag t, xs, v, h => by
    simp only [embedV] at h
    split at h
    · rename_i d n dt m hf hft
      obtain ⟨sv, h1, rfl⟩ := map_some.1 h
      obtain ⟨zs, hzs, hsv⟩ := bind_some.1 h1
      have hw := fill_width (mapM_lengths (w := 1) (fun a z hz => by
        obtain ⟨_, _, rfl⟩ := map_some.1 hz; rfl) _ _ hzs) hsv
      obtain ⟨hocc, hn⟩ := occupied_fill n 1 zs sv hsv
      have hc := collView_slots (d := d) (dt := dt) sv hw
      rw [hn] at hc
      simp only [decodeV, hf, hft, hc]
      show (occupied sv).mapM (fun | [z] => decodeV L t z | _ => none) = some xs
      rw [hocc]
      refine mapM_inverse (fun a z hz => ?_) _ _ hzs
      obtain ⟨z', hz', rfl⟩ := map_some.1 hz
      exact decode_embed t a z' hz'
    · cases h
  | .table k w, x, v, h => by
    simp only [embedV] at h
    split at h
    · rename_i d n dt m hf hft
      obtain ⟨sv, h1, rfl⟩ := map_some.1 h
      obtain ⟨zs, hzs, hsv⟩ := bind_some.1 h1
      have hw := fill_width (mapM_lengths (w := 2) (fun a z hz => by
        obtain ⟨_, _, h⟩ := bind_some.1 hz
        obtain ⟨_, _, rfl⟩ := map_some.1 h; rfl) _ _ hzs) hsv
      obtain ⟨hocc, hn⟩ := occupied_fill n 2 zs sv hsv
      have hc := collView_slots (d := d) (dt := dt) sv hw
      rw [hn] at hc
      have hx : zs.mapM (fun
          | [zk, zv] => (decodeV L k zk).bind fun a => (decodeV L w zv).map fun b => (a, b)
          | _ => none) = some x.1 := by
        refine mapM_inverse (fun a z hz => ?_) _ _ hzs
        obtain ⟨z1, hz1, h⟩ := bind_some.1 hz
        obtain ⟨z2, hz2, rfl⟩ := map_some.1 h
        simp [decode_embed k a.1 z1 hz1, decode_embed w a.2 z2 hz2]
      simp only [decodeV, hf, hft, hc]
      show ((occupied sv).mapM (fun
          | [zk, zv] => (decodeV L k zk).bind fun a => (decodeV L w zv).map fun b => (a, b)
          | _ => none)).bind (uniqueKeys (Ty.semWith Dsl.val k).2) = some x
      rw [hocc]; erw [hx]
      exact dite_eq_left x.2
    · cases h
theorem decodeVs_embed : (ts : List Ty) → (x : Ty.dens ts) → (vals : List Val) → embedVs L ts x = some vals →
    decodeVs L ts vals = some x
  | [], (), vals, h => by cases h; rfl
  | t :: ts, (x, xs), vals, h => by
    obtain ⟨v, hv, h⟩ := bind_some.1 h
    obtain ⟨vs, hvs, rfl⟩ := map_some.1 h
    simp [decodeVs, decode_embed t x v hv, decodeVs_embed ts xs vs hvs]; rfl
theorem decodeAlts_embed (d : Nat) : (k : Nat) → (vs : List (List Ty)) → (x : Ty.alts vs) → (v : Val) →
    embedAlts L d k vs x = some v → decodeAlts L d k vs v = some x
  | k, fs :: _, .inl x, v, h => by
    obtain ⟨vals, hv, rfl⟩ := map_some.1 h
    simp [decodeAlts, decodeVs_embed fs x vals hv]; rfl
  | k, _ :: vs, .inr y, v, h => by
    have h' : embedAlts L d (k + 1) vs y = some v := h
    have hy := decodeAlts_embed d (k + 1) vs y v h'
    obtain ⟨d', k', vals, rfl, hk⟩ := embedAlts_ctor d (k + 1) vs y _ h'
    have hne : ¬(d' = d ∧ k' = k) := fun ⟨_, h⟩ => by omega
    simp [decodeAlts, hne, hy]; rfl
/-- An embedded variant is a constructor from `k` on. -/
theorem embedAlts_ctor (d : Nat) : (k : Nat) → (vs : List (List Ty)) → (x : Ty.alts vs) → (v : Val) →
    embedAlts L d k vs x = some v → ∃ d' k' vals, v = .ctor d' k' vals ∧ k ≤ k'
  | k, fs :: _, .inl x, v, h => by
    obtain ⟨vals, _, rfl⟩ := map_some.1 h
    exact ⟨d, k, vals, rfl, Nat.le_refl k⟩
  | k, _ :: vs, .inr y, v, h => by
    obtain ⟨d', k', vals, rfl, hk⟩ := embedAlts_ctor d (k + 1) vs y v h
    exact ⟨d', k', vals, rfl, by omega⟩
end

/-- An embedded value is the value the SMT value codes. -/
theorem embed_rel (t : Ty) (x : t.den) (v : Val) (h : embedV L t x = some v) : RelV L t x v :=
  decode_rel t v x (decode_embed t x v h)

end

end Tazuna.Smt
