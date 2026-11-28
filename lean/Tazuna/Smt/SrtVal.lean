import Tazuna.Smt.Wf

/-! The models the proofs build are SMT-LIB structures: each variable holds a value of the sort its type is declared
at (`Val.InSrt`), free slots' items included. `fixV` puts any value in a data type's sort (`fixV_srtVal`), and an
embedded value's free slots hold `fixV`'s values, so an embedded value is in its sort too (`embedV_srtVal`). -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The value is one of the sort that codes the data type `t`, wherever the layout's datatypes and that sort are
found. -/
def SrtVal (L : Layout) (t : Ty) (w : Val) : Prop :=
  t.isData = true → ∀ dts σ, L.datatypes? = some dts → L.srt? t = some σ → Val.InSrt dts σ w

section
variable {L : Layout} {dts : List Datatype}

theorem mapM_getElem? {α β : Type} {f : α → Option β} : {xs : List α} → {ys : List β} → xs.mapM f = some ys →
    ∀ i : Nat, ys[i]? = xs[i]?.bind f
  | [], ys, h, i => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; simp
  | x :: xs, ys, h, i => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    cases i with
    | zero => simp [hy]
    | succ i => simp [mapM_getElem? hys i]

/-- A type the layout has is declared as its entry's datatype. -/
theorem find_datatype (hd : L.datatypes? = some dts) {t : Ty} {d n : Nat} (hf : L.find? t = some (d, n)) :
    ∃ D, L.datatype? (t, n) = some D ∧ dts[d]? = some D := by
  simp only [Layout.find?_eq, Option.map_eq_some_iff] at hf
  obtain ⟨⟨⟨u, m⟩, j⟩, hfind, he⟩ := hf
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨⟨hu⟩, -⟩ := Option.isSome_iff_exists.1 (by simpa using List.find?_some hfind :
    (Ty.same u t).isSome = true)
  subst hu
  have hget : L.types[j]? = some (u, m) := by simpa using List.mem_zipIdx_iff_getElem?.1 (List.mem_of_find?_eq_some hfind)
  have hall := mapM_isSome L.datatype? L.types
  rw [show L.types.mapM L.datatype? = L.datatypes? from rfl, hd] at hall
  have hsome := List.all_eq_true.1 hall.symm _ (List.mem_of_getElem? hget)
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.1 hsome
  refine ⟨D, hD, ?_⟩
  rw [mapM_getElem? hd j, hget, Option.bind_some, hD]

theorem inSrt_ctor {d k : Nat} {D : Datatype} {fs : List Srt} {vs : List Val} (hD : dts[d]? = some D)
    (hk : D.ctors[k]? = some fs) (h : Val.InSrts dts fs vs) : Val.InSrt dts (.dt d) (.ctor d k vs) := by
  simp only [Val.InSrt, hD, Option.bind_some, hk, Option.some.injEq, true_and]
  exact ⟨fs, rfl, h⟩

theorem inSrt_slots {d dt : Nat} {ss : List Srt} {sv : List (Bool × List Val)}
    (hD : dts[d]? = some ⟨[List.replicate sv.length (.dt dt)]⟩) (hT : dts[dt]? = some ⟨[.bool :: ss]⟩)
    (h : ∀ p ∈ sv, Val.InSrts dts ss p.2) : Val.InSrt dts (.dt d) (slotsVal d dt sv) :=
  inSrt_ctor hD rfl (go sv h)
where
  go : (sv : List (Bool × List Val)) → (∀ p ∈ sv, Val.InSrts dts ss p.2) →
      Val.InSrts dts (List.replicate sv.length (.dt dt)) (sv.map fun (b, vs) => .ctor dt 0 (.bool b :: vs))
    | [], _ => trivial
    | p :: sv, h => by
      simp only [List.length_cons, List.replicate_succ, List.map_cons, Val.InSrts]
      refine ⟨inSrt_ctor hT rfl ?_, go sv fun q hq => h q (by simp [hq])⟩
      simp only [Val.InSrts, Val.InSrt]
      exact ⟨trivial, h p (by simp)⟩

/-- A collection type the layout has is declared as `n` slots of its slot tuple, whose items have the sorts of the
item types. -/
theorem coll_dts (hd : L.datatypes? = some dts) {c : Ty} {item : List Ty} {d n : Nat} (hc : L.find? c = some (d, n))
    (hD : ∀ D, L.datatype? (c, n) = some D →
      ∃ s, L.srt? (.tuple (Ty.bool :: item)) = some s ∧ D = ⟨[List.replicate n s]⟩) :
    ∃ dt m ss, L.find? (.tuple (Ty.bool :: item)) = some (dt, m) ∧ item.mapM L.srt? = some ss ∧
      dts[d]? = some ⟨[List.replicate n (.dt dt)]⟩ ∧ dts[dt]? = some ⟨[.bool :: ss]⟩ := by
  obtain ⟨D, hD1, hD2⟩ := find_datatype hd hc
  obtain ⟨s, hs, rfl⟩ := hD D hD1
  simp only [Layout.srt?, Option.map_eq_some_iff] at hs
  obtain ⟨⟨dt, m⟩, hft, rfl⟩ := hs
  obtain ⟨E, hE1, hE2⟩ := find_datatype hd hft
  simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, List.mapM_cons, Option.bind_eq_some_iff,
    Option.some.injEq] at hE1
  obtain ⟨_, ⟨b, hb, ss, hss, rfl⟩, rfl⟩ := hE1
  have : b = .bool := by simpa [Ty.bool, Layout.srt?, boolVs?] using hb.symm
  subst this
  exact ⟨dt, m, ss, hft, hss, hD2, hE2⟩

theorem fixSlots_length (fix : List Val → List Val) : (n : Nat) → (vals : List Val) → (fixSlots fix n vals).length = n
  | 0, _ => rfl
  | n + 1, vals => by simp [fixSlots, fixSlots_length fix n vals.tail]

theorem fixSlots_mem {fix : List Val → List Val} : {n : Nat} → {vals : List Val} → {p : Bool × List Val} →
    p ∈ fixSlots fix n vals → ∃ zs, p.2 = fix zs
  | 0, _, _, h => by simp [fixSlots] at h
  | n + 1, vals, p, h => by
    simp only [fixSlots, List.mem_cons] at h
    rcases h with rfl | h
    · split <;> exact ⟨_, rfl⟩
    · exact fixSlots_mem h

/-- The sort of a found type: the datatype it is declared as. -/
theorem srt_dt {t : Ty} {σ : Srt} (hs : L.srt? t = some σ) (hi : t ≠ .int) (hdt : ∀ u, t ≠ .point u) (hstr : t ≠ .str)
    (hp : ∀ u, t ≠ .dsl .fresh u) (hb : ∀ a vs, t ≠ .adt 0 a vs) : ∃ d n, L.find? t = some (d, n) ∧ σ = .dt d := by
  unfold Layout.srt? at hs
  split at hs <;> first
    | (exfalso; first | exact hi rfl | exact hdt _ rfl | exact hstr rfl | exact hp _ rfl | exact hb _ _ rfl)
    | (obtain ⟨⟨d, n⟩, hf, rfl⟩ := Option.map_eq_some_iff.1 hs; exact ⟨d, n, hf, rfl⟩)

mutual
/-- `fixV` puts any value in the sort of a data type the layout has. -/
theorem fixV_inSrt (hd : L.datatypes? = some dts) : (t : Ty) → t.isData = true → (w : Val) → (σ : Srt) →
    L.srt? t = some σ → Val.InSrt dts σ (fixV L t w)
  | .int, _, w, σ, hs | .point _, _, w, σ, hs => by
    simp only [Layout.srt?, Option.some.injEq] at hs; subst hs
    unfold fixV; split <;> simp [Val.InSrt]
  | .dsl k a, hx, w, σ, hs => by
    simp only [Ty.isData, beq_iff_eq] at hx; subst hx
    simp only [Layout.srt?, Option.some.injEq] at hs; subst hs
    unfold fixV; split <;> simp [Val.InSrt]
  | .str, _, w, σ, hs => by
    simp only [Layout.srt?, Option.some.injEq] at hs; subst hs
    unfold fixV; split
    · split <;> simp_all [Val.InSrt]; rfl
    · simp [Val.InSrt]; rfl
  | .id, _, w, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨D, hD1, hD2⟩ := find_datatype hd hf
    simp only [Layout.datatype?, Option.some.injEq] at hD1; subst hD1
    unfold fixV; simp only [hf]
    split
    · exact inSrt_ctor hD2 rfl (by simp [Val.InSrts, Val.InSrt])
    · exact inSrt_ctor hD2 rfl (by split <;> simp_all [Val.InSrts, Val.InSrt]; rfl)
    · exact inSrt_ctor hD2 rfl (by simp [Val.InSrts, Val.InSrt]; rfl)
  | .adt 0 a vs, _, w, σ, hs => by
    simp only [Layout.srt?] at hs
    split at hs
    · simp only [Option.some.injEq] at hs; subst hs
      unfold fixV; split <;> simp [Val.InSrt]
    · cases hs
  | .adt (i + 1) a [], _, w, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨D, hD1, hD2⟩ := find_datatype hd hf
    simp only [Layout.datatype?, Option.some.injEq] at hD1; subst hD1
    unfold fixV; simp only [hf]
    split
    · split
      · simp_all
      · exact inSrt_ctor hD2 rfl trivial
    · exact inSrt_ctor hD2 rfl trivial
  | .adt (i + 1) a (fs :: rest), hx, w, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨D, hD1, hD2⟩ := find_datatype hd hf
    simp only [Ty.isData] at hx
    simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hD1
    obtain ⟨fss, hfss, rfl⟩ := hD1
    have hk : ∀ k vals, k < (fs :: rest).length → Val.InSrt dts (.dt d) (.ctor d k (fixAlts L (fs :: rest) k vals)) :=
      fun k vals hk => by
        obtain ⟨ss, hss, hin⟩ := fixAlts_inSrts hd (fs :: rest) hx k hk vals fss hfss
        exact inSrt_ctor hD2 hss hin
    unfold fixV; simp only [hf]
    split
    · split
      · exact hk _ _ (by assumption)
      · exact hk 0 [] (by simp)
    · exact hk 0 [] (by simp)
  | .tuple ts, hx, w, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨D, hD1, hD2⟩ := find_datatype hd hf
    simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hD1
    obtain ⟨ss, hss, rfl⟩ := hD1
    unfold fixV; simp only [hf]
    exact inSrt_ctor hD2 rfl (fixVs_inSrts hd ts (by simpa [Ty.isData] using hx) w.args ss hss)
  | .bag t, hx, w, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨dt, m, ss, hft, hss, hD, hT⟩ := coll_dts (item := [t]) hd hf fun D h => by
      simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨s, hs, rfl⟩ := h; exact ⟨s, hs, rfl⟩
    unfold fixV; simp only [hf, hft]
    refine inSrt_slots (by rw [fixSlots_length]; exact hD) hT fun p hp => ?_
    obtain ⟨zs, hz⟩ := fixSlots_mem hp
    rw [hz]
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hss
    obtain ⟨s, hs', _, rfl, rfl⟩ := hss
    exact ⟨fixV_inSrt hd t (by simpa [Ty.isData] using hx) _ s hs', trivial⟩
  | .list t, hx, w, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨dt, m, ss, hft, hss, hD, hT⟩ := coll_dts (item := [t]) hd hf fun D h => by
      simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨s, hs, rfl⟩ := h; exact ⟨s, hs, rfl⟩
    unfold fixV; simp only [hf, hft]
    refine inSrt_slots (by rw [fixSlots_length]; exact hD) hT fun p hp => ?_
    obtain ⟨zs, hz⟩ := fixSlots_mem hp
    rw [hz]
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hss
    obtain ⟨s, hs', _, rfl, rfl⟩ := hss
    exact ⟨fixV_inSrt hd t (by simpa [Ty.isData] using hx) _ s hs', trivial⟩
  | .table k v, hx, w, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨dt, m, ss, hft, hss, hD, hT⟩ := coll_dts (item := [k, v]) hd hf fun D h => by
      simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨s, hs, rfl⟩ := h; exact ⟨s, hs, rfl⟩
    unfold fixV; simp only [hf, hft]
    refine inSrt_slots (by rw [fixSlots_length]; exact hD) hT fun p hp => ?_
    obtain ⟨zs, hz⟩ := fixSlots_mem hp
    rw [hz]
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hss
    obtain ⟨sk, hsk, _, ⟨sv, hsv, _, rfl, rfl⟩, rfl⟩ := hss
    simp only [Ty.isData, Bool.and_eq_true] at hx
    exact ⟨fixV_inSrt hd k hx.1 _ sk hsk, fixV_inSrt hd v hx.2 _ sv hsv, trivial⟩
  | .fn ps r, _, w, σ, hs | .param _, _, w, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨D, hD1, -⟩ := find_datatype hd hf
    simp [Layout.datatype?] at hD1
theorem fixVs_inSrts (hd : L.datatypes? = some dts) : (ts : List Ty) → Ty.isDatas ts = true → (vals : List Val) →
    (ss : List Srt) → ts.mapM L.srt? = some ss → Val.InSrts dts ss (fixVs L ts vals)
  | [], _, _, ss, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; trivial
  | t :: ts, hx, vals, ss, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨s, hs, ss', hss, rfl⟩ := h
    simp only [Ty.isDatas, Bool.and_eq_true] at hx
    exact ⟨fixV_inSrt hd t hx.1 _ s hs, fixVs_inSrts hd ts hx.2 _ ss' hss⟩
theorem fixAlts_inSrts (hd : L.datatypes? = some dts) : (vs : List (List Ty)) → Ty.isDatass vs = true → (k : Nat) →
    k < vs.length → (vals : List Val) → (fss : List (List Srt)) → vs.mapM (·.mapM L.srt?) = some fss →
    ∃ ss, fss[k]? = some ss ∧ Val.InSrts dts ss (fixAlts L vs k vals)
  | [], _, _, hk, _, _, _ => by simp at hk
  | fs :: vs, hx, k, hk, vals, fss, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ss, hss, fss', hfss, rfl⟩ := h
    simp only [Ty.isDatass, Bool.and_eq_true] at hx
    cases k with
    | zero => exact ⟨ss, rfl, fixVs_inSrts hd fs hx.1 vals ss hss⟩
    | succ k => exact fixAlts_inSrts hd vs hx.2 k (by simpa using hk) vals fss' hfss
end

theorem fixV_srtVal (t : Ty) (w : Val) : SrtVal L t (fixV L t w) := fun hx _ σ hd hs => fixV_inSrt hd t hx w σ hs

theorem fill_mem {n : Nat} {item : List Val} {zs : List (List Val)} {sv : List (Bool × List Val)}
    (h : fillSlots n item zs = some sv) {p : Bool × List Val} (hp : p ∈ sv) : p.2 ∈ zs ∨ p.2 = item := by
  unfold fillSlots at h
  split at h
  · cases h
    simp only [List.mem_append, List.mem_map, List.mem_replicate] at hp
    rcases hp with ⟨z, hz, rfl⟩ | ⟨-, rfl⟩
    · exact .inl hz
    · exact .inr rfl
  · cases h

theorem mem_of_mapM {α β : Type} {f : α → Option β} {xs : List α} {ys : List β} (h : xs.mapM f = some ys)
    {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, f x = some y :=
  forall2_mem_left (mapM_forall2 (E := fun y x => f x = some y) (fun _ _ h => h) xs ys h) y hy

mutual
/-- An embedded value of a data type the layout has is in its sort: its free slots hold `fixV`'s items. -/
theorem embedV_inSrt (hd : L.datatypes? = some dts) : (t : Ty) → t.isData = true → (x : t.den) → (w : Val) →
    embedV L t x = some w → (σ : Srt) → L.srt? t = some σ → Val.InSrt dts σ w
  | .int, _, x, w, h, σ, hs | .point _, _, x, w, h, σ, hs => by
    simp only [Layout.srt?, Option.some.injEq] at hs; subst hs
    simp only [embedV, Option.some.injEq] at h; subst h; trivial
  | .dsl k a, hx, x, w, h, σ, hs => by
    simp only [Ty.isData, beq_iff_eq] at hx; subst hx
    simp only [Layout.srt?, Option.some.injEq] at hs; subst hs
    simp only [embedV, Option.some.injEq] at h; subst h; trivial
  | .str, _, x, w, h, σ, hs => by
    simp only [Layout.srt?, Option.some.injEq] at hs; subst hs
    simp only [embedV, Option.some.injEq] at h; subst h; exact x.2
  | .id, _, x, w, h, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨D, hD1, hD2⟩ := find_datatype hd hf
    simp only [Layout.datatype?, Option.some.injEq] at hD1; subst hD1
    simp only [embedV, hf, Option.map_some, Option.some.injEq] at h; subst h
    cases x with
    | fresh s i => exact inSrt_ctor hD2 rfl (by simp [Val.InSrts, Val.InSrt])
    | named s => exact inSrt_ctor hD2 rfl (by simpa [Val.InSrts, Val.InSrt] using s.2)
  | .adt 0 a vs, _, x, w, h, σ, hs => by
    simp only [Layout.srt?] at hs
    split at hs
    · rename_i hb
      obtain ⟨⟨rfl⟩, -⟩ := Option.isSome_iff_exists.1 hb
      simp only [Option.some.injEq] at hs; subst hs
      simp only [embedV, Option.some.injEq] at h; subst h; trivial
    · cases hs
  | .adt (i + 1) a [], _, x, _, _, _, _ => nomatch x
  | .adt (i + 1) a (fs :: rest), hx, x, w, h, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨D, hD1, hD2⟩ := find_datatype hd hf
    simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hD1
    obtain ⟨fss, hfss, rfl⟩ := hD1
    simp only [embedV, hf] at h
    obtain ⟨j, vals, ss, rfl, hss, hin⟩ := embedAlts_inSrt hd d 0 (fs :: rest) hx x w h fss hfss
    exact inSrt_ctor hD2 (by simpa using hss) hin
  | .tuple ts, hx, x, w, h, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨D, hD1, hD2⟩ := find_datatype hd hf
    simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hD1
    obtain ⟨ss, hss, rfl⟩ := hD1
    simp only [embedV, hf] at h
    obtain ⟨vals, hv, rfl⟩ := map_some.1 h
    exact inSrt_ctor hD2 rfl (embedVs_inSrts hd ts (by simpa [Ty.isData] using hx) x vals hv ss hss)
  | .bag t, hx, xs, w, h, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨dt, m, ss, hft, hss, hD, hT⟩ := coll_dts (item := [t]) hd hf fun D h => by
      simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨s, hs, rfl⟩ := h; exact ⟨s, hs, rfl⟩
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hss
    obtain ⟨s, hs', _, rfl, rfl⟩ := hss
    have hxt : t.isData = true := by simpa [Ty.isData] using hx
    simp only [embedV, hf, hft] at h
    obtain ⟨sv, h1, rfl⟩ := map_some.1 h
    obtain ⟨zs, hzs, hsv⟩ := bind_some.1 h1
    refine inSrt_slots (by rw [(occupied_fill n _ zs sv hsv).2]; exact hD) hT fun p hp => ?_
    rcases fill_mem hsv hp with hz | hz
    · obtain ⟨y, -, hy⟩ := mem_of_mapM hzs hz
      obtain ⟨z, hz', hz2⟩ := map_some.1 hy
      rw [← hz2]
      exact ⟨embedV_inSrt hd t hxt y z hz' s hs', trivial⟩
    · rw [hz]; exact ⟨fixV_inSrt hd t hxt _ s hs', trivial⟩
  | .list t, hx, xs, w, h, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨dt, m, ss, hft, hss, hD, hT⟩ := coll_dts (item := [t]) hd hf fun D h => by
      simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨s, hs, rfl⟩ := h; exact ⟨s, hs, rfl⟩
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hss
    obtain ⟨s, hs', _, rfl, rfl⟩ := hss
    have hxt : t.isData = true := by simpa [Ty.isData] using hx
    simp only [embedV, hf, hft] at h
    obtain ⟨sv, h1, rfl⟩ := map_some.1 h
    obtain ⟨zs, hzs, hsv⟩ := bind_some.1 h1
    refine inSrt_slots (by rw [(occupied_fill n _ zs sv hsv).2]; exact hD) hT fun p hp => ?_
    rcases fill_mem hsv hp with hz | hz
    · obtain ⟨y, -, hy⟩ := mem_of_mapM hzs hz
      obtain ⟨z, hz', hz2⟩ := map_some.1 hy
      rw [← hz2]
      exact ⟨embedV_inSrt hd t hxt y z hz' s hs', trivial⟩
    · rw [hz]; exact ⟨fixV_inSrt hd t hxt _ s hs', trivial⟩
  | .table k v, hx, x, w, h, σ, hs => by
    obtain ⟨d, n, hf, rfl⟩ := srt_dt hs (by simp) (by simp) (by simp) (by simp) (by simp)
    obtain ⟨dt, m, ss, hft, hss, hD, hT⟩ := coll_dts (item := [k, v]) hd hf fun D h => by
      simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨s, hs, rfl⟩ := h; exact ⟨s, hs, rfl⟩
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hss
    obtain ⟨sk, hsk, _, ⟨sv', hsv', _, rfl, rfl⟩, rfl⟩ := hss
    simp only [Ty.isData, Bool.and_eq_true] at hx
    simp only [embedV, hf, hft] at h
    obtain ⟨sv, h1, rfl⟩ := map_some.1 h
    obtain ⟨zs, hzs, hsv⟩ := bind_some.1 h1
    refine inSrt_slots (by rw [(occupied_fill n _ zs sv hsv).2]; exact hD) hT fun p hp => ?_
    rcases fill_mem hsv hp with hz | hz
    · obtain ⟨e, -, he⟩ := mem_of_mapM hzs hz
      obtain ⟨a, ha, he⟩ := bind_some.1 he
      obtain ⟨b, hb, he⟩ := map_some.1 he
      rw [← he]
      exact ⟨embedV_inSrt hd k hx.1 _ a ha sk hsk, embedV_inSrt hd v hx.2 _ b hb sv' hsv', trivial⟩
    · rw [hz]; exact ⟨fixV_inSrt hd k hx.1 _ sk hsk, fixV_inSrt hd v hx.2 _ sv' hsv', trivial⟩
  | .fn .., _, _, w, h, _, _ | .param _, _, _, w, h, _, _ => by simp [embedV] at h
theorem embedVs_inSrts (hd : L.datatypes? = some dts) : (ts : List Ty) → Ty.isDatas ts = true → (x : Ty.dens ts) →
    (vals : List Val) → embedVs L ts x = some vals → (ss : List Srt) → ts.mapM L.srt? = some ss →
    Val.InSrts dts ss vals
  | [], _, _, vals, h, ss, hs => by
    simp only [embedVs, Option.some.injEq] at h; subst h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hs; subst hs; trivial
  | t :: ts, hx, (x, xs), vals, h, ss, hs => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hs
    obtain ⟨s, hs1, ss', hss, rfl⟩ := hs
    simp only [Ty.isDatas, Bool.and_eq_true] at hx
    simp only [embedVs] at h
    obtain ⟨a, ha, h⟩ := bind_some.1 h
    obtain ⟨as, has, rfl⟩ := map_some.1 h
    exact ⟨embedV_inSrt hd t hx.1 x a ha s hs1, embedVs_inSrts hd ts hx.2 xs as has ss' hss⟩
theorem embedAlts_inSrt (hd : L.datatypes? = some dts) (d : Nat) : (k : Nat) → (vs : List (List Ty)) →
    Ty.isDatass vs = true → (x : Ty.alts vs) → (w : Val) → embedAlts L d k vs x = some w →
    (fss : List (List Srt)) → vs.mapM (·.mapM L.srt?) = some fss →
    ∃ j vals ss, w = .ctor d (k + j) vals ∧ fss[j]? = some ss ∧ Val.InSrts dts ss vals
  | k, fs :: _, hx, .inl x, w, h, fss, hf => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hf
    obtain ⟨ss, hss, fss', -, rfl⟩ := hf
    simp only [Ty.isDatass, Bool.and_eq_true] at hx
    simp only [embedAlts] at h
    obtain ⟨vals, hv, rfl⟩ := map_some.1 h
    exact ⟨0, vals, ss, rfl, rfl, embedVs_inSrts hd fs hx.1 x vals hv ss hss⟩
  | k, _ :: vs, hx, .inr y, w, h, fss, hf => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hf
    obtain ⟨_, -, fss', hfss, rfl⟩ := hf
    simp only [Ty.isDatass, Bool.and_eq_true] at hx
    simp only [embedAlts] at h
    obtain ⟨j, vals, ss, rfl, hss, hin⟩ := embedAlts_inSrt hd d (k + 1) vs hx.2 y w h fss' hfss
    exact ⟨j + 1, vals, ss, by rw [Nat.add_assoc, Nat.add_comm 1 j], hss, hin⟩
end

theorem embedV_srtVal {t : Ty} {x : t.den} {w : Val} (h : embedV L t x = some w) : SrtVal L t w :=
  fun hx _ σ hd hs => embedV_inSrt hd t hx x w h σ hs

/-! `fixV` keeps what the encoding reads of a value: a related value stays related (`fixV_relD`) and a value of the
type's shape keeps it (`fixV_sorted`); only free slots' items and parts outside the sort change. -/

theorem fixSlots_map (fix : List Val → List Val) (dt : Nat) : (sv : List (Bool × List Val)) →
    fixSlots fix sv.length (sv.map fun (b, vs) => .ctor dt 0 (.bool b :: vs)) = sv.map fun p => (p.1, fix p.2)
  | [] => rfl
  | p :: sv => by simp [fixSlots, fixSlots_map fix dt sv]

theorem occupied_fix (f : List Val → List Val) (sv : List (Bool × List Val)) :
    occupied (sv.map fun p => (p.1, f p.2)) = (occupied sv).map f := by
  induction sv with
  | nil => rfl
  | cons p sv ih =>
    obtain ⟨b, vs⟩ := p
    simp only [occupied, List.map_cons, List.filterMap_cons] at ih ⊢
    cases b <;> simp [ih]

theorem forall2_map_right {α : Type} {R S : α → List Val → Prop} {f : List Val → List Val}
    (h : ∀ a b, R a b → S a (f b)) : {as : List α} → {bs : List (List Val)} → Forall2 R as bs →
    Forall2 S as (bs.map f)
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨h _ _ h1, forall2_map_right h h2⟩

theorem holds2_fix {α : Type} {E E' : α → List Val → Prop} {f : List Val → List Val} (h : ∀ a b, E a b → E' a (f b))
    {ys : List α} {sv : List (Bool × List Val)} (h2 : Holds2 E ys sv) : Holds2 E' ys (sv.map fun p => (p.1, f p.2)) := by
  unfold Holds2 at *; rw [occupied_fix]; exact forall2_map_right h h2

/-- A collection value of slots `sv` fixed with the item fix `f`: the same slots with fixed items. -/
theorem fixV_slots {fix : List Val → List Val} {d dt n : Nat} {sv : List (Bool × List Val)} (hn : sv.length = n) :
    slotsVal d dt (fixSlots fix n (slotsVal d dt sv).args) = slotsVal d dt (sv.map fun p => (p.1, fix p.2)) := by
  subst hn; simp only [slotsVal, Val.args]; rw [fixSlots_map]

-- The fixed items of a slot are read from its first fields, as `fixV` reads them.
set_option linter.tazuna.silentDefault false in
mutual
theorem fixV_relD : (t : Ty) → (x : t.den0) → (w : Val) → RelD L t x w → RelD L t x (fixV L t w)
  | .int, _, _, h | .point _, _, _, h => by subst h; rfl
  | .str, x, _, h => by subst h; simp [fixV, x.2, RelD]
  | .id, x, _, ⟨d, n, hf, h⟩ => by
    subst h
    refine ⟨d, n, hf, ?_⟩
    cases x with
    | fresh s i => simp [fixV, hf, idVal]
    | named s => simp [fixV, hf, idVal, s.2]
  | .adt 0 _ vs, _, _, ⟨h, e⟩ => by subst h; subst e; exact ⟨rfl, rfl⟩
  | .adt (i + 1) a vs, x, w, ⟨d, n, hf, h⟩ => by
    obtain ⟨k, vals, rfl, -, hk, h'⟩ := fixAlts_relDAlts d 0 vs x w h
    refine ⟨d, n, hf, ?_⟩
    simp only [fixV, hf, Nat.sub_zero] at h' ⊢
    simp only [Nat.zero_add] at hk
    simp only [hk, ite_true]; exact h'
  | .tuple ts, x, _, ⟨d, n, vals, hf, rfl, h⟩ => ⟨d, n, _, hf, by simp [fixV, hf, Val.args], fixVs_relDs ts x vals h⟩
  | .bag t, xs, _, ⟨d, n, dt, m, sv, hl, hp, hn, rfl, hw, ys, hys, h2⟩ => by
    refine ⟨d, n, dt, m, sv.map fun p => (p.1, [fixV L t (p.2.headD default)]), hl, hp, by simpa using hn, by simp only [fixV, hl, hp]; exact fixV_slots hn,
      fun p hp => ?_, ys, hys, ?_⟩
    · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp; rfl
    · exact holds2_fix (E := fun y vs => ∃ z, vs = [z] ∧ RelD L t y z) (f := fun vs => [fixV L t (vs.headD default)])
        (fun y vs ⟨z, e, hz⟩ => ⟨_, by subst e; rfl, fixV_relD t y z hz⟩) h2
  | .list t, xs, _, ⟨d, n, dt, m, sv, hl, hp, hn, rfl, hw, h2⟩ => by
    refine ⟨d, n, dt, m, sv.map fun p => (p.1, [fixV L t (p.2.headD default)]), hl, hp, by simpa using hn, by simp only [fixV, hl, hp]; exact fixV_slots hn,
      fun p hp => ?_, ?_⟩
    · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp; rfl
    · exact holds2_fix (E := fun y vs => ∃ z, vs = [z] ∧ RelD L t y z) (f := fun vs => [fixV L t (vs.headD default)])
        (fun y vs ⟨z, e, hz⟩ => ⟨_, by subst e; rfl, fixV_relD t y z hz⟩) h2
  | .table k v, x, _, ⟨d, n, dt, m, sv, hl, hp, hn, rfl, hw, ys, hys, h2⟩ => by
    refine ⟨d, n, dt, m, sv.map fun p => (p.1, [fixV L k (p.2.headD default), fixV L v (p.2.tail.headD default)]), hl, hp, by simpa using hn, by simp only [fixV, hl, hp]; exact fixV_slots hn,
      fun p hp => ?_, ys, hys, ?_⟩
    · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp; rfl
    · exact holds2_fix (E := fun e vs => ∃ zk zv, vs = [zk, zv] ∧ RelD L k e.1 zk ∧ RelD L v e.2 zv)
        (f := fun vs => [fixV L k (vs.headD default), fixV L v (vs.tail.headD default)]) (fun e vs ⟨zk, zv, he, hk, hv⟩ =>
        ⟨_, _, by subst he; rfl, fixV_relD k e.1 zk hk, fixV_relD v e.2 zv hv⟩) h2
  | .dsl k a, x, w, h => by
    cases k <;> simp only [RelD] at h
    subst h; rfl
  | .fn .., _, _, h | .param _, _, _, h => h.elim
theorem fixVs_relDs : (ts : List Ty) → (x : (Ty.semsWith Dsl.base ts).1) → (vals : List Val) → RelDs L ts x vals →
    RelDs L ts x (fixVs L ts vals)
  | [], _, _, h => by cases h; rfl
  | t :: ts, (x, xs), _, ⟨w, ws, rfl, hw, hws⟩ => ⟨_, _, rfl, fixV_relD t x w hw, fixVs_relDs ts xs ws hws⟩
theorem fixAlts_relDAlts (d : Nat) : (j : Nat) → (vs : List (List Ty)) → (x : (Ty.semAltsWith Dsl.base vs).1) →
    (w : Val) → RelDAlts L d j vs x w →
    ∃ k vals, w = .ctor d k vals ∧ j ≤ k ∧ k < j + vs.length ∧
      RelDAlts L d j vs x (.ctor d k (fixAlts L vs (k - j) vals))
  | j, fs :: _, .inl x, _, ⟨vals, rfl, h⟩ => by
    refine ⟨j, vals, rfl, Nat.le_refl j, by simp, ?_⟩
    simp only [Nat.sub_self, fixAlts]
    exact ⟨_, rfl, fixVs_relDs fs x vals h⟩
  | j, _ :: vs, .inr y, w, h => by
    obtain ⟨k, vals, rfl, hj, hk, h'⟩ := fixAlts_relDAlts d (j + 1) vs y w h
    refine ⟨k, vals, rfl, by omega, by simp only [List.length_cons]; omega, ?_⟩
    have e : k - j = (k - (j + 1)) + 1 := by omega
    rw [e]; exact h'
end

theorem collView_fix {fix : List Val → List Val} {d dt n w : Nat} {v : Val} {sv : List (Bool × List Val)}
    (h : collView d dt n w v = some sv) (hf : ∀ vs, (fix vs).length = w) :
    collView d dt n w (slotsVal d dt (fixSlots fix n v.args)) = some (sv.map fun p => (p.1, fix p.2)) := by
  obtain ⟨rfl, hn, -⟩ := collView_eq h
  rw [fixV_slots hn, ← hn]
  have := collView_slots (d := d) (dt := dt) (w := w) (sv.map fun p => (p.1, fix p.2)) fun p hp => by
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp; exact hf _
  simpa using this

-- The fixed items of a slot are read from its first fields, as `fixV` reads them.
set_option linter.tazuna.silentDefault false in
mutual
theorem fixV_sorted : (t : Ty) → (w : Val) → Sorted L t w → Sorted L t (fixV L t w)
  | .int, _, ⟨n, e⟩ | .point _, _, ⟨n, e⟩ => by subst e; exact ⟨n, rfl⟩
  | .str, _, ⟨s, hs, e⟩ => by subst e; exact ⟨s, hs, by simp [fixV, hs]⟩
  | .id, _, ⟨d, n, hf, h⟩ => by
    refine ⟨d, n, hf, ?_⟩
    rcases h with ⟨m, i, rfl⟩ | ⟨s, hs, rfl⟩
    · exact .inl ⟨m, i, by simp [fixV, hf]⟩
    · exact .inr ⟨s, hs, by simp [fixV, hf, hs]⟩
  | .adt 0 _ vs, _, ⟨h, b, e⟩ => by subst e; exact ⟨h, b, rfl⟩
  | .adt (i + 1) a [], w, ⟨d, n, hf, h, e⟩ => by
    subst e; exact ⟨d, n, hf, rfl, by simp [fixV, hf, fixAlts]⟩
  | .adt (i + 1) a (fs :: rest), w, ⟨d, n, hf, h⟩ => by
    obtain ⟨k, vals, rfl, -, hk, h'⟩ := fixAlts_sortedAlts d 0 (fs :: rest) w h (by simp)
    refine ⟨d, n, hf, ?_⟩
    simp only [Nat.zero_add] at hk
    simp only [fixV, hf, hk, ite_true, Nat.sub_zero] at h' ⊢
    exact h'
  | .tuple ts, _, ⟨d, n, vals, hf, rfl, h⟩ => ⟨d, n, _, hf, by simp [fixV, hf, Val.args], fixVs_sorted ts vals h⟩
  | .bag t, w, ⟨d, n, dt, m, sv, hl, hp, hc, h⟩ => by
    refine ⟨d, n, dt, m, sv.map fun p => (p.1, [fixV L t (p.2.headD default)]), hl, hp, ?_, fun p hp' hb z hz => ?_⟩
    · simp only [fixV, hl, hp]
      exact collView_fix (fix := fun zs => [fixV L t (zs.headD default)]) hc (fun _ => rfl)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp'
      obtain ⟨-, -, hw⟩ := collView_eq hc
      match hq2 : q.2, hw q hq with
      | [z'], _ =>
        simp only [hq2, List.headD_cons, List.cons.injEq, and_true] at hz
        subst hz
        exact fixV_sorted t z' (h q hq hb z' hq2)
  | .list t, w, ⟨d, n, dt, m, sv, hl, hp, hc, h⟩ => by
    refine ⟨d, n, dt, m, sv.map fun p => (p.1, [fixV L t (p.2.headD default)]), hl, hp, ?_, fun p hp' hb z hz => ?_⟩
    · simp only [fixV, hl, hp]
      exact collView_fix (fix := fun zs => [fixV L t (zs.headD default)]) hc (fun _ => rfl)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp'
      obtain ⟨-, -, hw⟩ := collView_eq hc
      match hq2 : q.2, hw q hq with
      | [z'], _ =>
        simp only [hq2, List.headD_cons, List.cons.injEq, and_true] at hz
        subst hz
        exact fixV_sorted t z' (h q hq hb z' hq2)
  | .table k v, w, ⟨d, n, dt, m, sv, hl, hp, hc, h⟩ => by
    refine ⟨d, n, dt, m, sv.map fun p => (p.1, [fixV L k (p.2.headD default), fixV L v (p.2.tail.headD default)]),
      hl, hp, ?_, fun p hp' hb zk zv hz => ?_⟩
    · simp only [fixV, hl, hp]
      exact collView_fix (fix := fun zs => [fixV L k (zs.headD default), fixV L v (zs.tail.headD default)]) hc
        (fun _ => rfl)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp'
      obtain ⟨-, -, hw⟩ := collView_eq hc
      match hq2 : q.2, hw q hq with
      | [zk', zv'], _ =>
        simp only [hq2, List.headD_cons, List.tail_cons, List.cons.injEq, and_true] at hz
        obtain ⟨rfl, rfl⟩ := hz
        obtain ⟨h1, h2⟩ := h q hq hb zk' zv' hq2
        exact ⟨fixV_sorted k zk' h1, fixV_sorted v zv' h2⟩
  | .dsl k a, w, h => by
    cases k <;> simp only [Sorted] at h
    obtain ⟨n, rfl⟩ := h; exact ⟨n, rfl⟩
  | .fn .., _, h | .param _, _, h => h.elim
theorem fixVs_sorted : (ts : List Ty) → (vals : List Val) → SortedVs L ts vals → SortedVs L ts (fixVs L ts vals)
  | [], [], _ => trivial
  | t :: ts, w :: ws, ⟨h1, h2⟩ => ⟨fixV_sorted t w h1, fixVs_sorted ts ws h2⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim
theorem fixAlts_sortedAlts (d : Nat) : (j : Nat) → (vs : List (List Ty)) → (w : Val) → SortedAlts L d j vs w →
    vs ≠ [] → ∃ k vals, w = .ctor d k vals ∧ j ≤ k ∧ k < j + vs.length ∧
      SortedAlts L d j vs (.ctor d k (fixAlts L vs (k - j) vals))
  | _, [], _, _, h => absurd rfl h
  | j, fs :: vs, _, ⟨k, vals, rfl, h⟩, _ => by
    rcases h with ⟨rfl, h⟩ | ⟨hne, h⟩
    · refine ⟨k, vals, rfl, Nat.le_refl k, by simp, ?_⟩
      simp only [Nat.sub_self, fixAlts]
      exact ⟨k, _, rfl, .inl ⟨rfl, fixVs_sorted fs vals h⟩⟩
    · cases vs with
      | nil => exact absurd h.1 (by omega)
      | cons fs' vs' =>
        obtain ⟨k', vals', e, hj, hk, h'⟩ := fixAlts_sortedAlts d (j + 1) (fs' :: vs') _ h (by simp)
        cases e
        refine ⟨k, vals, rfl, by omega, by simp only [List.length_cons] at hk ⊢; omega, ?_⟩
        have e : k - j = (k - (j + 1)) + 1 := by omega
        rw [e]
        exact ⟨k, _, rfl, .inr ⟨hne, h'⟩⟩
end

theorem srtVal_int {t : Ty} {n : Int} (h : Sorted L t (.int n)) : SrtVal L t (.int n) := by
  intro _ _ σ _ hs
  cases t with
  | int | point _ => simp only [Layout.srt?, Option.some.injEq] at hs; subst hs; trivial
  | dsl k a =>
    cases k <;> simp only [Sorted] at h
    simp only [Layout.srt?, Option.some.injEq] at hs; subst hs; trivial
  | adt i a vs =>
    cases i with
    | zero => simp [Sorted] at h
    | succ i =>
      obtain ⟨d, n, -, h⟩ := h
      cases vs <;> simp [SortedAlts] at h
  | _ => simp [Sorted, collView] at h

end

end Tazuna.Smt
