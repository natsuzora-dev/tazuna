import Tazuna.Smt.StepNoGap
import Tazuna.Smt.Unroll
import Tazuna.Smt.Timer
import Tazuna.Smt.Pair

/-! The layout boundary: every script builder prove and generate call, run in a checked service's layout, refuses only
for the spec's reasons, never for a gap of the layout (`Sound`). One fact about the layout carries most of it: every
datatype the layout holds has a sort for each field, so `datatypes?` is found (`datatypes_ofParts`). Each lookup a
builder makes at a type refuses with that type's own limit where it has no term (`lacks`, `lacksData`), so a gap is
left only where the layout has the type, which `Avail` rules out. The commands read a builder's result only through
`Sound.get`, which needs the builder's theorem, so a new builder cannot reach them without one; what is left of a
refusal is the spec's (a `Limit`, an Undecided line) or a case the loaded program's types rule out (`Unexpected`,
exit 4, excluded by the loader's typing rather than by a theorem). -/

namespace Tazuna.Smt
open Tazuna.Ir
namespace Layout

theorem srt_isSome_le {L L' : Layout} (h : Le L L') : (t : Ty) → (L.srt? t).isSome = true → (L'.srt? t).isSome = true
  | .int, _ | .str, _ | .date, _ => rfl
  | .adt 0 _ vs, hs => by simpa [srt?] using hs
  | .dsl .fresh _, _ => rfl
  | .tuple _, hs | .adt (_ + 1) _ _, hs | .id, hs | .list _, hs | .bag _, hs | .table _ _, hs | .fn _ _, hs
  | .param _, hs => by simp only [srt?, Option.isSome_map] at hs ⊢; exact isSome_le h hs
  | .dsl k a, hs => by
    cases k <;> first | rfl | (simp only [srt?, Option.isSome_map] at hs ⊢; exact isSome_le h hs)

/-- What a layout entry's datatype needs: a sort for each field of each constructor. -/
def DtCond (L : Layout) : Ty → Prop
  | .tuple ts => ∀ u ∈ ts, (L.srt? u).isSome = true
  | .adt _ _ vs => ∀ fs ∈ vs, ∀ u ∈ fs, (L.srt? u).isSome = true
  | .id => True
  | .bag t | .list t => (L.srt? (.tuple [Ty.bool, t])).isSome = true
  | .table k w => (L.srt? (.tuple [Ty.bool, k, w])).isSome = true
  | .dsl .effect [e] => ∀ fs ∈ L.effectFields e, ∀ u ∈ fs, (L.srt? u).isSome = true
  | _ => False

theorem mapM_mapM_isSome {α β : Type} (f : α → Option β) (vs : List (List α)) :
    (vs.mapM (fun fs : List α => fs.mapM f)).isSome = true ↔ ∀ fs ∈ vs, ∀ u ∈ fs, (f u).isSome = true := by
  rw [mapM_isSome_iff]; exact forall₂_congr fun fs _ => mapM_isSome_iff f fs

theorem datatype_isSome_iff (L : Layout) (t : Ty) (n : Nat) : (L.datatype? (t, n)).isSome = true ↔ L.DtCond t := by
  cases t with
  | tuple ts =>
    simp only [datatype?, DtCond]
    rw [← mapM_isSome_iff]; cases ts.mapM L.srt? <;> simp
  | adt i a vs =>
    cases vs with
    | nil => simp [datatype?, DtCond]
    | cons fs vs =>
      simp only [datatype?, DtCond]
      rw [← mapM_mapM_isSome]; cases (fs :: vs).mapM (fun fs : List Ty => fs.mapM L.srt?) <;> simp
  | id => simp [datatype?, DtCond]
  | bag t | list t => simp only [datatype?, DtCond]; cases L.srt? (.tuple [Ty.bool, t]) <;> simp
  | table k w => simp only [datatype?, DtCond]; cases L.srt? (.tuple [Ty.bool, k, w]) <;> simp
  | dsl k a =>
    match k, a with
    | .effect, [e] =>
      simp only [datatype?, DtCond]
      split
      · rename_i h; simp [h]
      · rw [← mapM_mapM_isSome]; cases (L.effectFields e).mapM (fun fs : List Ty => fs.mapM L.srt?) <;> simp
    | .effect, [] | .effect, _ :: _ :: _ | .spec, _ | .service, _ | .command, _ | .query, _ | .machine, _
    | .reaction, _ | .external, _ | .externalCommand, _ | .externalQuery, _ | .source, _ | .declared, _
    | .subscription, _ | .bounds, _ | .create, _ | .response, _ | .scenario, _ | .step, _ | .sender, _
    | .closure, _ | .effectClosure, _ | .fresh, _ => simp [datatype?, DtCond]
  | int | str | date | fn | param => simp [datatype?, DtCond]

theorem dtCond_le {L L' : Layout} (h : Le L L') : (t : Ty) → L.DtCond t → L'.DtCond t
  | .tuple _, c => fun u hu => srt_isSome_le h u (c u hu)
  | .adt _ _ _, c => fun fs hfs u hu => srt_isSome_le h u (c fs hfs u hu)
  | .id, c => c
  | .bag _, c | .list _, c | .table _ _, c => srt_isSome_le h _ c
  | .dsl .effect [e], c => by
    simp only [DtCond, effectFields_le h] at c ⊢; exact fun fs hfs u hu => srt_isSome_le h u (c fs hfs u hu)
  | .int, c | .str, c | .date, c | .fn _ _, c | .param _, c => c.elim
  | .dsl .fresh _, c => c.elim


theorem srt_of_find {L : Layout} : (t : Ty) → t.sorted = true → (L.find? t).isSome = true → (L.srt? t).isSome = true
  | .int, _, _ | .str, _, _ | .date, _, _ => rfl
  | .adt 0 _ vs, ht, _ => by simpa [srt?, Ty.sorted] using ht
  | .dsl .fresh _, _, _ => rfl
  | .tuple _, _, hf | .adt (_ + 1) _ _, _, hf | .id, _, hf | .list _, _, hf | .bag _, _, hf | .table _ _, _, hf
  | .fn _ _, _, hf | .param _, _, hf => by simpa only [srt?, Option.isSome_map] using hf
  | .dsl k a, _, hf => by cases k <;> first | rfl | simpa only [srt?, Option.isSome_map] using hf

theorem srt_bool (L : Layout) : (L.srt? Ty.bool).isSome = true := rfl

/-- Every entry's datatype has a sort for each of its fields. -/
def DtsOk (L : Layout) : Prop := ∀ p ∈ L.types, L.DtCond p.1

theorem dtsOk_push {L : Layout} (h : DtsOk L) (t : Ty) (n : Nat) (ht : (L.push t n).DtCond t) : DtsOk (L.push t n) := by
  intro p hp
  unfold push at hp ht ⊢
  split at hp
  · rename_i hs; simp only [hs, ↓reduceIte] at ht ⊢; exact h p hp
  · rename_i hs
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at ht ⊢
    rcases List.mem_append.1 hp with hp | hp
    · exact dtCond_le (push_le L t n |> fun hl => by unfold push at hl; simpa [hs] using hl) _ (h p hp)
    · simp only [List.mem_singleton] at hp; subst hp; exact ht

section
variable {slots : Ty → Nat} {dsl : Layout → Dsl → List Ty → Layout} (ok : Ty → Prop)

theorem addTyWith_srt
    (hdsl : ∀ L e, ok (.dsl .effect [e]) → ((dsl L .effect [e]).find? (.dsl .effect [e])).isSome = true) (L : Layout) (t : Ty) (hok : ok t) (ht : t.sorted = true) :
    ((addTyWith slots dsl L t).srt? t).isSome = true := by
  cases t with
  | tuple | adt _ _ _ | id | list | bag | table =>
    first
    | exact srt_of_find _ ht (find?_push _ _ _)
    | (rename_i i a vs; cases i with
        | zero => simpa [srt?, Ty.sorted] using ht
        | succ i => exact srt_of_find _ ht (find?_push _ _ _))
  | dsl k a =>
    match k, a with
    | .effect, [e] => exact srt_of_find _ ht (hdsl L e hok)
    | .fresh, _ => rfl
    | .effect, [] | .effect, _ :: _ :: _ | .spec, _ | .service, _ | .command, _ | .query, _ | .machine, _
    | .reaction, _ | .external, _ | .externalCommand, _ | .externalQuery, _ | .source, _ | .declared, _
    | .subscription, _ | .bounds, _ | .create, _ | .response, _ | .scenario, _ | .step, _ | .sender, _
    | .closure, _ | .effectClosure, _ => simp [Ty.sorted] at ht
  | int | str | date => rfl
  | fn | param => simp [Ty.sorted] at ht

theorem addTysWith_srt (hd : ∀ L k a, Le L (dsl L k a))
    (hdsl : ∀ L e, ok (.dsl .effect [e]) → ((dsl L .effect [e]).find? (.dsl .effect [e])).isSome = true) : (L : Layout) → (ts : List Ty) → ∀ t ∈ ts, ok t → t.sorted = true →
    ((addTysWith slots dsl L ts).srt? t).isSome = true
  | _, [], _, h, _, _ => nomatch h
  | L, u :: us, t, hm, hok, ht => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact srt_isSome_le (addTysWith_le hd _ us) _ (addTyWith_srt ok hdsl L t hok ht)
    · exact addTysWith_srt hd hdsl _ us t hm hok ht

theorem addTyssWith_srt (hd : ∀ L k a, Le L (dsl L k a))
    (hdsl : ∀ L e, ok (.dsl .effect [e]) → ((dsl L .effect [e]).find? (.dsl .effect [e])).isSome = true) : (L : Layout) → (vs : List (List Ty)) → ∀ fs ∈ vs, ∀ t ∈ fs, ok t → t.sorted = true →
    ((addTyssWith slots dsl L vs).srt? t).isSome = true
  | _, [], _, h, _, _, _, _ => nomatch h
  | L, gs :: vs, fs, hm, t, ht, hok, hs => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact srt_isSome_le (addTyssWith_le hd _ vs) _ (addTysWith_srt ok hd hdsl L fs t ht hok hs)
    · exact addTyssWith_srt hd hdsl _ vs fs hm t ht hok hs

/-- `ok` holds of every part of a type it holds of. -/
structure OkClosed : Prop where
  tuple : ∀ ts, ok (.tuple ts) → ∀ t ∈ ts, ok t
  adt : ∀ i a vs, ok (.adt i a vs) → ∀ fs ∈ vs, ∀ t ∈ fs, ok t
  list : ∀ t, ok (.list t) → ok t
  bag : ∀ t, ok (.bag t) → ok t
  table : ∀ k w, ok (.table k w) → ok k ∧ ok w
  fn : ∀ ps r, ok (.fn ps r) → (∀ p ∈ ps, ok p) ∧ ok r

theorem sortedss_mem : {vs : List (List Ty)} → Ty.sortedss vs = true → ∀ fs ∈ vs, Ty.sorteds fs = true
  | _ :: _, h, _, .head _ => by simp only [Ty.sortedss, Bool.and_eq_true] at h; exact h.1
  | _ :: _, h, fs, .tail _ hf => by simp only [Ty.sortedss, Bool.and_eq_true] at h; exact sortedss_mem h.2 fs hf

theorem sorted_slot {t : Ty} (ht : t.sorted = true) : (Ty.tuple [Ty.bool, t]).sorted = true := by
  simp [Ty.sorted, Ty.sorteds, Ty.bool, boolVs?, ht]

theorem sorted_slot2 {k w : Ty} (hk : k.sorted = true) (hw : w.sorted = true) :
    (Ty.tuple [Ty.bool, k, w]).sorted = true := by
  simp [Ty.sorted, Ty.sorteds, Ty.bool, boolVs?, hk, hw]

variable (hc : OkClosed ok) (hd : ∀ L k a, Le L (dsl L k a))
  (hdsl : ∀ L e, ok (.dsl .effect [e]) → ((dsl L .effect [e]).find? (.dsl .effect [e])).isSome = true)
  (K : Layout) (hds : ∀ L k a, Le K L → DtsOk L → ok (.dsl k a) → (Ty.dsl k a).sortable = true → DtsOk (dsl L k a))
include hc hd hdsl hds

-- The three theorems use the hypotheses through one another.
set_option linter.unusedSectionVars false in
mutual
theorem addTyWith_dts : (L : Layout) → Le K L → DtsOk L → (t : Ty) → ok t → t.sortable = true →
    DtsOk (addTyWith slots dsl L t)
  | L, hK, h, .tuple ts, hok, ht => by
    have hs : Ty.sorteds ts = true := by simpa [Ty.sortable, Ty.sorted] using ht
    exact dtsOk_push (addTysWith_dts L hK h ts fun t ht' => ⟨hc.tuple ts hok t ht', sortable_of_sorted t (sorteds_mem hs t ht')⟩)
      _ _ fun u hu => srt_isSome_le (push_le _ _ _) u
        (addTysWith_srt ok hd hdsl L ts u hu (hc.tuple ts hok u hu) (sorteds_mem hs u hu))
  | L, _, h, .adt 0 a vs, _, ht => by
    simp only [addTyWith]; split
    · exact h
    · rename_i hb; simp [Ty.sortable, Ty.sorted, hb] at ht
  | L, hK, h, .adt (i + 1) a vs, hok, ht => by
    have hs : Ty.sortedss vs = true := by simpa [Ty.sortable, Ty.sorted] using ht
    exact dtsOk_push (addTyssWith_dts L hK h vs (hc.adt _ a vs hok) hs) _ _ fun fs hfs u hu =>
      srt_isSome_le (push_le _ _ _) u (addTyssWith_srt ok hd hdsl L vs fs hfs u hu (hc.adt _ a vs hok fs hfs u hu)
        (sorteds_mem (sortedss_mem hs fs hfs) u hu))
  | L, _, h, .id, _, _ => dtsOk_push h _ _ trivial
  | L, hK, h, .list t, hok, ht => by
    have hs : t.sorted = true := by simpa [Ty.sortable, Ty.sorted] using ht
    refine dtsOk_push (dtsOk_push (addTyWith_dts L hK h t (hc.list t hok) (sortable_of_sorted t hs)) _ _ ?_) _ _
      (srt_of_find _ (sorted_slot hs) (isSome_le (push_le _ _ _) (find?_push _ _ _)))
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact srt_bool _
    · exact srt_isSome_le (push_le _ _ _) _ (addTyWith_srt ok hdsl L u (hc.list u hok) hs)
  | L, hK, h, .bag t, hok, ht => by
    have hs : t.sorted = true := by simpa [Ty.sortable, Ty.sorted] using ht
    refine dtsOk_push (dtsOk_push (addTyWith_dts L hK h t (hc.bag t hok) (sortable_of_sorted t hs)) _ _ ?_) _ _
      (srt_of_find _ (sorted_slot hs) (isSome_le (push_le _ _ _) (find?_push _ _ _)))
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact srt_bool _
    · exact srt_isSome_le (push_le _ _ _) _ (addTyWith_srt ok hdsl L u (hc.bag u hok) hs)
  | L, hK, h, .table k w, hok, ht => by
    have hs : k.sorted = true ∧ w.sorted = true := by simpa [Ty.sortable, Ty.sorted] using ht
    have hk1 := addTyWith_dts L hK h k (hc.table k w hok).1 (sortable_of_sorted k hs.1)
    have hw1 := addTyWith_dts _ (hK.trans (addTyWith_le hd L k)) hk1 w (hc.table k w hok).2 (sortable_of_sorted w hs.2)
    refine dtsOk_push (dtsOk_push hw1 _ _ ?_) _ _
      (srt_of_find _ (sorted_slot2 hs.1 hs.2) (isSome_le (push_le _ _ _) (find?_push _ _ _)))
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl
    · exact srt_bool _
    · exact srt_isSome_le ((addTyWith_le hd _ w).trans (push_le _ _ _)) _
        (addTyWith_srt ok hdsl L u (hc.table u w hok).1 hs.1)
    · exact srt_isSome_le (push_le _ _ _) _ (addTyWith_srt ok hdsl _ u (hc.table k u hok).2 hs.2)
  | L, hK, h, .fn ps r, hok, ht => by
    simp only [Ty.sortable, Bool.and_eq_true] at ht
    exact addTyWith_dts _ (hK.trans (addTysWith_le hd L ps)) (addTysWith_dts L hK h ps fun p hp => ⟨(hc.fn ps r hok).1 p hp, sortables_mem (slots := slots) (dsl := dsl) (K := L) ht.1 p hp⟩) r
      (hc.fn ps r hok).2 ht.2
  | L, hK, h, .dsl k a, hok, ht => hds L k a hK h hok ht
  | _, _, h, .int, _, _ | _, _, h, .str, _, _ | _, _, h, .date, _, _ | _, _, h, .param _, _, _ => h
theorem addTysWith_dts : (L : Layout) → Le K L → DtsOk L → (ts : List Ty) → (∀ t ∈ ts, ok t ∧ t.sortable = true) →
    DtsOk (addTysWith slots dsl L ts)
  | _, _, h, [], _ => h
  | L, hK, h, t :: ts, ht => addTysWith_dts _ (hK.trans (addTyWith_le hd L t)) (addTyWith_dts L hK h t (ht t (by simp)).1 (ht t (by simp)).2) ts
      fun t' h' => ht t' (by simp [h'])
theorem addTyssWith_dts : (L : Layout) → Le K L → DtsOk L → (vs : List (List Ty)) → (∀ fs ∈ vs, ∀ t ∈ fs, ok t) →
    Ty.sortedss vs = true → DtsOk (addTyssWith slots dsl L vs)
  | _, _, h, [], _, _ => h
  | L, hK, h, ts :: vs, hok, hv => by
    simp only [Ty.sortedss, Bool.and_eq_true] at hv
    exact addTyssWith_dts _ (hK.trans (addTysWith_le hd L ts)) (addTysWith_dts L hK h ts fun t ht => ⟨hok ts (by simp) t ht,
      sortable_of_sorted t (sorteds_mem hv.1 t ht)⟩) vs (fun fs hfs => hok fs (by simp [hfs])) hv.2
end

end

theorem dataMem : {ts : List Ty} → Ty.isDatas ts = true → ∀ t ∈ ts, t.isData = true
  | _ :: _, h, _, .head _ => by simp only [Ty.isDatas, Bool.and_eq_true] at h; exact h.1
  | _ :: _, h, t, .tail _ ht => by simp only [Ty.isDatas, Bool.and_eq_true] at h; exact dataMem h.2 t ht

theorem datasMem : {vs : List (List Ty)} → Ty.isDatass vs = true → ∀ fs ∈ vs, Ty.isDatas fs = true
  | _ :: _, h, _, .head _ => by simp only [Ty.isDatass, Bool.and_eq_true] at h; exact h.1
  | _ :: _, h, fs, .tail _ hf => by simp only [Ty.isDatass, Bool.and_eq_true] at h; exact datasMem h.2 fs hf

theorem okClosed_isData : OkClosed (fun t => t.isData = true) where
  tuple ts h t ht := by simp only [Ty.isData] at h; exact dataMem h t ht
  adt i a vs h fs hfs t ht := by simp only [Ty.isData] at h; exact dataMem (datasMem h fs hfs) t ht
  list t h := by simpa [Ty.isData] using h
  bag t h := by simpa [Ty.isData] using h
  table k w h := by simpa [Ty.isData] using h
  fn ps r h := by simp only [Ty.isData, Bool.and_eq_true] at h; exact ⟨dataMem h.1, h.2⟩

theorem okClosed_true : OkClosed (fun _ => True) :=
  ⟨fun _ _ _ _ => trivial, fun _ _ _ _ _ _ _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial,
    fun _ _ _ => ⟨trivial, trivial⟩, fun _ _ _ => ⟨fun _ _ => trivial, trivial⟩⟩

theorem fold_dts (slots : Ty → Nat) : (fss : List (List Ty)) → (∀ fs ∈ fss, ∀ t ∈ fs, t.isData = true ∧ t.sorted = true) →
    (L : Layout) → DtsOk L → DtsOk (fss.foldl (fun L fs => addTysWith slots (fun L _ _ => L) L fs) L)
  | [], _, _, h => h
  | fs :: fss, hf, L, h => fold_dts slots fss (fun fs' h' => hf fs' (by simp [h'])) _
      (addTysWith_dts (fun t => t.isData = true) okClosed_isData (fun L _ _ => Le.refl L)
        (fun _ _ he => by simp [Ty.isData] at he) L (fun _ _ _ _ h _ _ => h) L (Le.refl L) h fs
        fun t ht => ⟨(hf fs (by simp) t ht).1, sortable_of_sorted t (hf fs (by simp) t ht).2⟩)

theorem fold_srt (slots : Ty → Nat) : (fss : List (List Ty)) → (L : Layout) → ∀ fs ∈ fss, ∀ t ∈ fs, t.isData = true →
    t.sorted = true → ((fss.foldl (fun L fs => addTysWith slots (fun L _ _ => L) L fs) L).srt? t).isSome = true
  | [], _, _, h, _, _, _, _ => nomatch h
  | gs :: fss, L, fs, hm, t, ht, hd, hs => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact srt_isSome_le (fold_le slots fss _) _ (addTysWith_srt (fun t => t.isData = true) (fun L _ _ => Le.refl L)
        (fun _ _ he => by simp [Ty.isData] at he) L fs t ht hd hs)
    · exact fold_srt slots fss _ fs hm t ht hd hs

theorem addEffect_dts (slots : Ty → Nat) (L : Layout) (e : Ty) (h : DtsOk L)
    (hk : ∀ fs ∈ L.effectFields e, ∀ t ∈ fs, t.isData = true ∧ t.sorted = true) : DtsOk (addEffect slots L e) := by
  refine dtsOk_push (fold_dts slots _ hk L h) _ _ ?_
  have hf := effectFields_le (addEffect_le slots L e) e
  unfold addEffect at hf
  show ∀ fs ∈ _, _
  rw [hf]
  exact fun fs hfs u hu => srt_isSome_le (push_le _ _ _) u
    (fold_srt slots _ L fs hfs u hu (hk fs hfs u hu).1 (hk fs hfs u hu).2)

/-- Every datatype `addTys` adds, from a layout without datatypes, has a sort for each field, given kinds whose fields
are data with sorts. -/
theorem addTys_dts (slots : Ty → Nat) (L : Layout) (hL : L.types = [])
    (hk : ∀ e, ∀ fs ∈ L.effectFields e, ∀ t ∈ fs, t.isData = true ∧ t.sorted = true) (ts : List Ty)
    (hts : ∀ t ∈ ts, t.sortable = true) : DtsOk (addTys slots L ts) := by
  unfold addTys
  refine addTysWith_dts (fun _ => True) okClosed_true ?_ ?_ L ?_ L (Le.refl L) (fun p hp => by simp [hL] at hp) ts
    fun t ht => ⟨trivial, hts t ht⟩
  · intro L' k a
    match k, a with
    | .effect, [e] => exact addEffect_le _ L' e
    | .effect, [] | .effect, _ :: _ :: _ | .spec, _ | .service, _ | .command, _ | .query, _ | .machine, _
    | .reaction, _ | .external, _ | .externalCommand, _ | .externalQuery, _ | .source, _ | .declared, _
    | .subscription, _ | .bounds, _ | .create, _ | .response, _ | .scenario, _ | .step, _ | .sender, _
    | .closure, _ | .effectClosure, _ | .fresh, _ => exact Le.refl L'
  · intro L' e _; exact find?_push _ _ _
  · intro L' k a hK h' _ _
    match k, a with
    | .effect, [e] =>
      exact addEffect_dts _ L' e h' (by rw [effectFields_le hK]; exact hk e)
    | .effect, [] | .effect, _ :: _ :: _ | .spec, _ | .service, _ | .command, _ | .query, _ | .machine, _
    | .reaction, _ | .external, _ | .externalCommand, _ | .externalQuery, _ | .source, _ | .declared, _
    | .subscription, _ | .bounds, _ | .create, _ | .response, _ | .scenario, _ | .step, _ | .sender, _
    | .closure, _ | .effectClosure, _ | .fresh, _ => exact h'

end Layout

/-- The service's layout declares every datatype it holds: each has a sort for every field, so its `datatypes?` is
found. -/
theorem datatypes_ofParts (p : ProgramParts) (v : ServiceV) : ∃ dts, (Layout.ofParts p v).datatypes? = some dts := by
  obtain ⟨hK, hO⟩ := kindsOf_fields p v
  have h := Layout.addTys_dts (listSlots (stepSlots v p.lits) p.lits) (Layout.kindsOf p v) rfl (fun e fs hfs t ht => by
      simp only [Layout.effectFields, Layout.effectsOf, Layout.ownsOf, List.mem_append, List.mem_map,
        List.mem_filter] at hfs
      have hdata : ∀ {fs : List Ty}, Ty.sorteds fs = true ∧ (Ty.tuple fs).isData = true → t ∈ fs →
          t.isData = true ∧ t.sorted = true := fun hf ht' =>
        ⟨Layout.dataMem (by simpa [Ty.isData] using hf.2) t ht', Layout.sorteds_mem hf.1 t ht'⟩
      rcases hfs with ⟨k, ⟨hk, -⟩, rfl⟩ | ⟨k, ⟨hk, -⟩, rfl⟩
      · exact hdata (hK k hk) ht
      · exact hdata (hO k hk) ht)
    ((stepTys v ++ p.tys ++ useTys v (Layout.kindsOf p v)).filter Ty.sortable) (fun t ht => (List.mem_filter.1 ht).2)
  exact Option.isSome_iff_exists.1 ((mapM_isSome_iff _ _).2 fun q hq => (Layout.datatype_isSome_iff _ q.1 q.2).2 (h q hq))

section
variable {L : Layout}

theorem srt_of_has : (t : Ty) → L.Has t → t.sorted = true → (L.srt? t).isSome = true
  | .tuple _, ⟨_, hf⟩, hs | .adt (_ + 1) _ _, ⟨_, hf⟩, hs => Layout.srt_of_find _ hs hf
  | .id, hf, hs => Layout.srt_of_find _ hs hf
  | .list _, ⟨_, _, hf⟩, hs | .bag _, ⟨_, _, hf⟩, hs => Layout.srt_of_find _ hs hf
  | .table _ _, ⟨_, _, _, hf⟩, hs => Layout.srt_of_find _ hs hf
  | .adt 0 _ _, _, hs => by simpa [Layout.srt?, Ty.sorted] using hs
  | .int, _, _ | .str, _, _ | .date, _, _ => rfl
  | .fn _ _, _, hs | .param _, _, hs => by simp [Ty.sorted] at hs
  | .dsl k a, hh, hs => by
    match k, a with
    | .effect, [e] => exact Layout.srt_of_find _ hs hh.2
    | .fresh, _ => rfl
    | .effect, [] | .effect, _ :: _ :: _ | .spec, _ | .service, _ | .command, _ | .query, _ | .machine, _
    | .reaction, _ | .external, _ | .externalCommand, _ | .externalQuery, _ | .source, _ | .declared, _
    | .subscription, _ | .bounds, _ | .create, _ | .response, _ | .scenario, _ | .step, _ | .sender, _
    | .closure, _ | .effectClosure, _ => simp [Ty.sorted] at hs

/-- A lookup refused as `lacks t` is no gap where the layout has `t`'s datatypes whenever it has a sort and the lookup
finds them. -/
theorem sound_lacks_sorted {α : Type} {t : Ty} {o : Option α} (ha : Avail L t)
    (hf : t.sorted = true → L.Has t → o.isSome = true) : Sound (fun a => o = some a) (need (lacks t) o) :=
  sound_need fun ho => by
    cases hg : (lacks t).gap with
    | false => rfl
    | true => have hs := lacks_gap hg; have := hf hs (ha hs); simp [ho] at this

theorem sound_srt {t : Ty} (ha : Avail L t) : Sound (fun a => L.srt? t = some a) (need (lacks t) (L.srt? t)) :=
  sound_lacks_sorted ha fun hs hh => srt_of_has t hh hs

/-- A lookup refused as `lacksData t` is no gap where the layout has `t`'s datatypes whenever it has a sort and the
lookup finds a term for every value with one. -/
theorem sound_lacksData {α : Type} {t : Ty} {o : Option α} (ha : Avail L t)
    (hf : L.Has t → t.embeddable = true → t.plainKeys = true → o.isSome = true) :
    Sound (fun a => o = some a) (need (lacksData t) o) :=
  sound_need fun ho => by
    unfold lacksData
    split
    · rfl
    · split
      · rfl
      · rename_i he hk
        simp only [Bool.not_eq_true', Bool.not_eq_false] at he hk
        have := hf (ha (sorted_of_embeddable t (by simpa using he))) (by simpa using he) (by simpa using hk)
        simp [ho] at this

theorem sound_lacksDatas {α : Type} {ts : List Ty} {o : Option α} (ha : ∀ t ∈ ts, Avail L t)
    (hf : (∀ t ∈ ts, L.Has t ∧ t.embeddable = true ∧ t.plainKeys = true) → o.isSome = true) :
    Sound (fun a => o = some a) (need (lacksDatas ts) o) :=
  sound_need fun ho => by
    unfold lacksDatas
    split
    · rename_i t ht
      have hm := List.mem_of_find?_eq_some ht
      have hb := List.find?_some ht
      unfold lacksData
      split
      · rfl
      · split
        · rfl
        · rename_i he hk; simp_all
    · rename_i hn
      have := hf fun t ht => by
        have hb := List.find?_eq_none.1 hn t ht
        simp only [Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
        have he : t.embeddable = true := by
          cases h : t.embeddable
          · simp [h] at hb
          · rfl
        exact ⟨ha t ht (sorted_of_embeddable t he), he, by simpa [he] using hb⟩
      simp [ho] at this

end

section
variable {L : Layout} {D : Dsl → List Ty → Prop} (n : Term)

mutual
/-- The names term of a value of a type with an SMT value is built wherever the layout holds the type's datatypes. -/
theorem namesT_isSome : (t : Ty) → Layout.HasWith L D t → t.embeddable = true → (x : Term) →
    (namesT L n t x).isSome = true
  | .int, _, _, _ | .str, _, _, _ | .date, _, _, _ | .adt 0 _ _, _, _, _ => rfl
  | .id, hh, _, _ => by simp only [namesT, Option.isSome_map]; exact hh
  | .dsl k a, _, he, x => by simp only [Ty.embeddable, beq_iff_eq] at he; subst he; rfl
  | .adt (i + 1) a vs, ⟨hvs, hf⟩, he, x => by
    obtain ⟨⟨d, m⟩, hd⟩ := Option.isSome_iff_exists.1 hf
    simp only [Ty.embeddable] at he
    simp only [namesT, hd, Option.bind_some]
    exact namesAlts_isSome d 0 vs hvs he x
  | .tuple ts, ⟨hts, hf⟩, he, x => by
    obtain ⟨⟨d, m⟩, hd⟩ := Option.isSome_iff_exists.1 hf
    simp only [Ty.embeddable] at he
    simp only [namesT, hd, Option.bind_some]
    exact namesFields_isSome d 0 ts hts he x 0
  | .bag t, ⟨ht, hf1, hf2⟩, he, x => by
    obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 hf1
    obtain ⟨⟨d, k⟩, hd⟩ := Option.isSome_iff_exists.1 hf2
    simp only [Ty.embeddable] at he
    simp only [namesT, hd, hdt, Option.isSome_map]
    exact mapM_some_of fun sl _ => by rw [Option.isSome_map]; exact namesT_isSome t ht he _
  | .list t, ⟨ht, hf1, hf2⟩, he, x => by
    obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 hf1
    obtain ⟨⟨d, k⟩, hd⟩ := Option.isSome_iff_exists.1 hf2
    simp only [Ty.embeddable] at he
    simp only [namesT, hd, hdt, Option.isSome_map]
    exact mapM_some_of fun sl _ => by rw [Option.isSome_map]; exact namesT_isSome t ht he _
  | .table k w, ⟨hk, hw, hf1, hf2⟩, he, x => by
    obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 hf1
    obtain ⟨⟨d, j⟩, hd⟩ := Option.isSome_iff_exists.1 hf2
    simp only [Ty.embeddable, Bool.and_eq_true] at he
    simp only [namesT, hd, hdt, Option.isSome_map]
    refine mapM_some_of fun sl _ => ?_
    rw [Option.isSome_map]
    obtain ⟨ck, hck⟩ := Option.isSome_iff_exists.1 (namesT_isSome k hk he.1 sl.2[0])
    obtain ⟨cw, hcw⟩ := Option.isSome_iff_exists.1 (namesT_isSome w hw he.2 sl.2[1])
    simp [hck, hcw]
  | .fn .., _, he, _ | .param _, _, he, _ => by simp [Ty.embeddable] at he
theorem namesFields_isSome (d k : Nat) : (ts : List Ty) → Layout.HasWiths L D ts → Ty.embeddables ts = true →
    (x : Term) → (j : Nat) → (namesFields L n d k ts x j).isSome = true
  | [], _, _, _, _ => rfl
  | t :: ts, ⟨ht, hts⟩, he, x, j => by
    simp only [Ty.embeddables, Bool.and_eq_true] at he
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (namesT_isSome t ht he.1 (.sel d k j x))
    simp only [namesFields, hc, Option.bind_some, Option.isSome_map]
    exact namesFields_isSome d k ts hts he.2 x (j + 1)
theorem namesAlts_isSome (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Layout.HasWithss L D vs →
    Ty.embeddabless vs = true → (x : Term) → (namesAlts L n d k vs x).isSome = true
  | _, [], _, _, _ => rfl
  | k, fs :: vs, ⟨hfs, hvs⟩, he, x => by
    simp only [Ty.embeddabless, Bool.and_eq_true] at he
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (namesFields_isSome d k fs hfs he.1 x 0)
    simp only [namesAlts, hc, Option.bind_some, Option.isSome_map]
    exact namesAlts_isSome d (k + 1) vs hvs he.2 x
end

end

section
variable {L : Layout} (hL : SortedLayout L)
include hL

theorem collT_isSome {c : Ty} {item : List Ty} {xs : List (SlotItems item.length)} {d n : Nat}
    (hc : L.find? c = some (d, n)) (ht : (L.find? (.tuple (Ty.bool :: item))).isSome = true)
    (hi : ∀ u ∈ item, L.Has u ∧ u.sorted = true) (hlen : xs.length ≤ n) : (collT L c item xs).isSome = true := by
  obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 ht
  have hdef : (item.mapM (defaultT L)).isSome = true :=
    (mapM_isSome_iff _ _).2 fun u hu => defaultT_isSome hL (hi u hu).1 (hi u hu).2
  obtain ⟨ds, hds⟩ := Option.isSome_iff_exists.1 hdef
  have hd : ∃ y, (defaultItems L item).toOption = some y := by
    unfold defaultItems; split
    · exact ⟨_, rfl⟩
    · rename_i h; rw [h] at hds; cases hds
  obtain ⟨y, hy⟩ := hd
  simp [collT, hc, hdt, hy, hlen]

omit hL in
theorem bind_isSome {α β : Type} {x : Option α} {f : α → Option β} (h : (x.bind f).isSome = true) :
    ∃ a, x = some a ∧ (f a).isSome = true := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- A collection's items with SMT values, within the slots, have a constant term. -/
theorem collItems_isSome {α : Type} {c : Ty} {item : List Ty} {xs : List α} {d n : Nat}
    (hc : L.find? c = some (d, n)) (ht : (L.find? (.tuple (Ty.bool :: item))).isSome = true)
    (hi : ∀ u ∈ item, L.Has u ∧ u.sorted = true) {e : α → Option (List Val)} {g : α → Option (SlotItems item.length)}
    (heg : ∀ x ∈ xs, (e x).isSome = true → (g x).isSome = true) {fv : List Val}
    (he : ((xs.mapM e).bind (fillSlots n fv)).isSome = true) :
    ((xs.mapM g).bind (collT L c item)).isSome = true := by
  obtain ⟨zs, hzs, hfill⟩ := bind_isSome he
  have hle := (fillSlots_isSome n fv zs).1 hfill
  rw [mapM_some_length e xs zs hzs] at hle
  obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.1
    ((mapM_isSome_iff g xs).2 fun x hx => heg x hx ((mapM_isSome_iff e xs).1 (by simp [hzs]) x hx))
  rw [hys, Option.bind_some]
  exact collT_isSome hL hc ht hi (by rw [mapM_some_length g xs ys hys]; exact hle)

-- The three theorems use `hL` through one another.
set_option linter.unusedSectionVars false in
mutual
/-- A value with an SMT value (`embedV`) has a constant term too, wherever the layout has its type's datatypes: the
term only adds default items in the free slots, which every sorted type has. -/
theorem dataT_isSome : (t : Ty) → L.Has t → t.sorted = true → (x : t.den) → (embedV L t x).isSome = true →
    (dataT L t x).isSome = true
  | .int, _, _, _, _ | .str, _, _, _, _ | .date, _, _, _, _ => rfl
  | .id, _, _, _, he => by simpa [dataT, embedV] using he
  | .adt 0 a vs, _, _, x, he => by
    simp only [Ty.sorted] at *
    obtain ⟨⟨rfl⟩⟩ := Option.isSome_iff_exists.1 (by assumption : (boolVs? vs).isSome = true)
    rfl
  | .adt (i + 1) a vs, ⟨hvs, hf⟩, hs, x, he => by
    obtain ⟨⟨d, m⟩, hd⟩ := Option.isSome_iff_exists.1 hf
    simp only [embedV, hd] at he
    simp only [dataT, hd]
    exact dataAlts_isSome d 0 vs hvs (by simpa [Ty.sorted] using hs) x he
  | .tuple ts, ⟨hts, hf⟩, hs, x, he => by
    obtain ⟨⟨d, m⟩, hd⟩ := Option.isSome_iff_exists.1 hf
    simp only [embedV, hd, Option.isSome_map] at he
    simp only [dataT, hd, Option.isSome_map]
    exact dataTs_isSome ts hts (by simpa [Ty.sorted] using hs) x he
  | .bag t, ⟨ht, hf1, hf2⟩, hs, xs, he => by
    obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 hf1
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hf2
    have hst : t.sorted = true := by simpa [Ty.sorted] using hs
    simp only [embedV, hd, hdt, Option.isSome_map] at he
    exact collItems_isSome hL hd hf1 (by simp [ht, hst]) (fun x _ hx => by
      rw [Option.isSome_map] at hx ⊢; exact dataT_isSome t ht hst x hx) he
  | .list t, ⟨ht, hf1, hf2⟩, hs, xs, he => by
    obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 hf1
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hf2
    have hst : t.sorted = true := by simpa [Ty.sorted] using hs
    simp only [embedV, hd, hdt, Option.isSome_map] at he
    exact collItems_isSome hL hd hf1 (by simp [ht, hst]) (fun x _ hx => by
      rw [Option.isSome_map] at hx ⊢; exact dataT_isSome t ht hst x hx) he
  | .table k w, ⟨hk, hw, hf1, hf2⟩, hs, x, he => by
    obtain ⟨⟨dt, m⟩, hdt⟩ := Option.isSome_iff_exists.1 hf1
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hf2
    have hst : k.sorted = true ∧ w.sorted = true := by simpa [Ty.sorted] using hs
    simp only [embedV, hd, hdt, Option.isSome_map] at he
    refine collItems_isSome hL hd hf1 (by simp [hk, hw, hst]) (fun e _ hx => ?_) he
    obtain ⟨a, ha, hb⟩ := bind_isSome hx
    rw [Option.isSome_map] at hb
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.1 (dataT_isSome k hk hst.1 e.1 (by simp [ha]))
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (dataT_isSome w hw hst.2 e.2 hb)
    simp [ha', hb']
  | .dsl k a, _, hs, x, he => by
    match k, a with
    | .fresh, _ => rfl
    | .effect, [e] => simp [embedV] at he
    | .effect, [] | .effect, _ :: _ :: _ | .spec, _ | .service, _ | .command, _ | .query, _ | .machine, _
    | .reaction, _ | .external, _ | .externalCommand, _ | .externalQuery, _ | .source, _ | .declared, _
    | .subscription, _ | .bounds, _ | .create, _ | .response, _ | .scenario, _ | .step, _ | .sender, _
    | .closure, _ | .effectClosure, _ => simp [Ty.sorted] at hs
  | .fn .., _, hs, _, _ | .param _, _, hs, _, _ => by simp [Ty.sorted] at hs
theorem dataTs_isSome : (ts : List Ty) → Layout.HasWiths L (Layout.HasDsl L) ts → Ty.sorteds ts = true →
    (x : Ty.dens ts) → (embedVs L ts x).isSome = true → (dataTs L ts x).isSome = true
  | [], _, _, _, _ => rfl
  | t :: ts, ⟨ht, hts⟩, hs, (x, xs), he => by
    simp only [Ty.sorteds, Bool.and_eq_true] at hs
    obtain ⟨a, ha, he⟩ := bind_isSome he
    rw [Option.isSome_map] at he
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.1 (dataT_isSome t ht hs.1 x (by simp [ha]))
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (dataTs_isSome ts hts hs.2 xs he)
    simp [dataTs, ha', hb']
theorem dataAlts_isSome (d : Nat) : (k : Nat) → (vs : List (List Ty)) → Layout.HasWithss L (Layout.HasDsl L) vs →
    Ty.sortedss vs = true → (x : Ty.alts vs) → (embedAlts L d k vs x).isSome = true → (dataAlts L d k vs x).isSome = true
  | k, fs :: _, ⟨hfs, _⟩, hs, .inl x, he => by
    simp only [Ty.sortedss, Bool.and_eq_true] at hs
    simp only [embedAlts, Option.isSome_map] at he
    simp only [dataAlts, Option.isSome_map]
    exact dataTs_isSome fs hfs hs.1 x he
  | k, _ :: vs, ⟨_, hvs⟩, hs, .inr y, he => by
    simp only [Ty.sortedss, Bool.and_eq_true] at hs
    exact dataAlts_isSome d (k + 1) vs hvs hs.2 y he
end

end

section
variable {L : Layout} (hL : SortedLayout L)
include hL

theorem tablesOf_isSome {v : ServiceV} : (ms : List (MachineV v.records v.event)) →
    (∀ m ∈ ms, L.Has m.table ∧ m.table.sorted = true) → (initState.tablesOf L v ms).isSome = true
  | [], _ => rfl
  | m :: ms, h => by
    obtain ⟨⟨hk, hw, ht, hf⟩, hs⟩ := h m (by simp)
    obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hf
    have hst : m.key.sorted = true ∧ m.state.sorted = true := by
      simpa [MachineV.table, Ty.sorted] using hs
    obtain ⟨t, htt⟩ := Option.isSome_iff_exists.1 (collT_isSome hL (xs := []) hd ht
      (by simp [hk, hw, hst]) (by simp))
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (tablesOf_isSome ms fun m' hm' => h m' (by simp [hm']))
    simp only [initState.tablesOf, MachineV.table] at htt ⊢
    simp [htt, hu]

end

/-- A checked service's initial state has constant terms in its layout wherever its records have an SMT value: the
pending table and the instance tables start empty. -/
theorem initState_ofService (c : CheckedSpec) {v : ServiceV} (hv : v ∈ c.spec.services)
    (he : (embedV (Layout.ofService c.program.defs v) v.records (Ty.up _ v.records_data v.init)).isSome = true) :
    (initState (Layout.ofService c.program.defs v) v).isSome = true := by
  have hk := c.checked v hv
  have hs := stepTys_has c.program.defs hk
  have hL := sorted_ofParts c.program.defs.parts v
  obtain ⟨⟨her, -⟩, hms, hep, -, -⟩ := stateTys_iff.1 hk.stateTys
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1
    (dataT_isSome hL v.records (hs _ (by simp [stepTys])) (sorted_of_embeddable _ her) _ he)
  have hp : (Layout.ofService c.program.defs v).Has (pendingTable (shapes v)) := hs _ (by simp [stepTys])
  obtain ⟨-, hw1, ht1, hf1⟩ := hp
  obtain ⟨⟨d, n⟩, hd⟩ := Option.isSome_iff_exists.1 hf1
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (collT_isSome hL (xs := []) hd ht1
    (fun u hu => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact ⟨trivial, rfl⟩
      · exact ⟨hw1, sorted_of_embeddable _ hep⟩) (by simp))
  obtain ⟨tb, htb⟩ := Option.isSome_iff_exists.1 (tablesOf_isSome hL v.machines fun m hm =>
    ⟨hs _ (by simp only [stepTys]; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hm))),
      sorted_of_embeddable _ (hms m hm).1⟩)

  simp [initState, hr, pendingTable, hq, htb]

theorem mem_placeKinds {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat} :
    (ks : List (Nat × (Nat → SymInput v shs n))) → (b : Nat) → ∀ inp ∈ (placeKinds ks b).1, ∃ k ∈ ks, ∃ b', inp = k.2 b'
  | [], _, _, h => by simp [placeKinds] at h
  | (w, f) :: ks, b, inp, h => by
    simp only [placeKinds, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨(w, f), by simp, b, rfl⟩
    · obtain ⟨k, hk, b', rfl⟩ := mem_placeKinds ks (b + w) inp h
      exact ⟨k, by simp [hk], b', rfl⟩

section
variable (c : CheckedSpec) (v : ServiceV)

/-- The types of an input kind's terms and values have their datatypes in the service's layout wherever they have
sorts. -/
def KindAvail {n : Nat} (inp : SymInput v (shapes v) n) : Prop :=
  (∀ t ∈ inp.tys, Avail (Layout.ofService c.program.defs v) t) ∧
    ∀ t ∈ inp.dataTys, Avail (Layout.ofService c.program.defs v) t

theorem kindAvail {n : Nat} (inp : SymInput v (shapes v) n) (hu : ∀ t a b, inp ≠ .unmatched t a b) :
    KindAvail c v inp := by
  have hcaller := avail_stepTy c v (t := v.caller) (by simp [stepTys])
  cases inp with
  | command i x y =>
    have hi := avail_use c v (t := (v.commands.get i).input) (by
      simp only [useTys, List.mem_append, List.mem_flatMap, List.mem_cons]
      exact .inl (.inl (.inl (.inl (.inr ⟨_, List.get_mem _ i, by simp⟩)))))
    simp only [List.get_eq_getElem] at hi
    exact ⟨by simp [SymInput.tys, hcaller, hi], by simp [SymInput.dataTys, hcaller, hi]⟩
  | query i x y =>
    have hi := avail_use c v (t := (v.queries.get i).input) (by
      simp only [useTys, List.mem_append, List.mem_flatMap, List.mem_cons]
      exact .inl (.inl (.inl (.inr ⟨_, List.get_mem _ i, by simp⟩))))
    simp only [List.get_eq_getElem] at hi
    exact ⟨by simp [SymInput.tys, hcaller, hi], by simp [SymInput.dataTys, hcaller, hi]⟩
  | answer j k x y =>
    have hi := avail_use c v (t := answerTy (shapes v)[j].output (shapes v)[j].rejection) (by
      simp only [useTys, List.mem_append, List.mem_map]
      exact .inl (.inr ⟨_, List.getElem_mem _, rfl⟩))
    have hi' : Avail (Layout.ofService c.program.defs v) (answerTy (shapes v)[j.1].output (shapes v)[j.1].rejection) := hi
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simp only [SymInput.tys, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact avail_int
      · exact hi'
    · simp only [SymInput.dataTys, List.mem_cons, List.not_mem_nil, or_false] at ht
      subst ht; exact hi'
  | unmatched t x y => exact absurd rfl (hu t x y)
  | event i x =>
    have hi := avail_use c v (t := (v.subscribes.get i).event) (by
      simp only [useTys, List.mem_append, List.mem_map]
      exact .inl (.inl (.inr ⟨_, List.get_mem _ i, rfl⟩)))
    simp only [List.get_eq_getElem] at hi
    exact ⟨by simp [SymInput.tys, hi], by simp [SymInput.dataTys, hi]⟩
  | clock x =>
    exact ⟨fun t ht => by simp only [SymInput.tys, List.mem_singleton] at ht; subst ht; exact avail_int,
      by simp [SymInput.dataTys]⟩

theorem unrollKinds_avail {n : Nat} {a : Bool} : ∀ k ∈ unrollKinds v (shapes v) n a, ∀ b, KindAvail c v (k.2 b) := by
  intro k hk b
  simp only [unrollKinds, List.mem_append, List.mem_map, List.mem_finRange, true_and, List.mem_singleton] at hk
  rcases hk with (((⟨i, rfl⟩ | ⟨i, rfl⟩) | hk) | ⟨i, rfl⟩) | rfl
  · exact kindAvail c v _ fun _ _ _ h => by cases h
  · exact kindAvail c v _ fun _ _ _ h => by cases h
  · split at hk
    · simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hk
      obtain ⟨j, -, x, rfl⟩ := hk
      exact kindAvail c v _ fun _ _ _ h => by cases h
    · simp at hk
  · exact kindAvail c v _ fun _ _ _ h => by cases h
  · exact kindAvail c v _ fun _ _ _ h => by cases h

theorem stepInputs_avail {n b : Nat} : ∀ inp ∈ stepInputs v (shapes v) n b, KindAvail c v inp := by
  intro inp hinp
  refine kindAvail c v inp fun t x y h => ?_
  subst h
  simp [stepInputs] at hinp

end

section
variable {L : Layout} {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat}

theorem inputWf_isSome (inp : SymInput v shs n)
    (h : ∀ t ∈ inp.dataTys, L.Has t ∧ t.embeddable = true ∧ t.plainKeys = true) : (inp.wf L).isSome = true := by
  have w := fun t (ht : t ∈ inp.dataTys) x => wfT_isSome t (h t ht).1 (h t ht).2.1 (h t ht).2.2 x
  cases inp with
  | command i caller input =>
    obtain ⟨c1, h1⟩ := Option.isSome_iff_exists.1 (w v.caller (by simp [SymInput.dataTys]) caller)
    obtain ⟨c2, h2⟩ := Option.isSome_iff_exists.1 (w (v.commands.get i).input (by simp [SymInput.dataTys]) input)
    simp only [List.get_eq_getElem] at h2; simp [SymInput.wf, h1, h2]
  | query i caller input =>
    obtain ⟨c1, h1⟩ := Option.isSome_iff_exists.1 (w v.caller (by simp [SymInput.dataTys]) caller)
    obtain ⟨c2, h2⟩ := Option.isSome_iff_exists.1 (w (v.queries.get i).input (by simp [SymInput.dataTys]) input)
    simp only [List.get_eq_getElem] at h2; simp [SymInput.wf, h1, h2]
  | answer k j to value | unmatched t to value | event i value =>
    simp only [SymInput.wf, Option.isSome_map]; exact w _ (by simp [SymInput.dataTys]) value
  | clock => rfl

theorem validT_sound (inp : SymInput v (shapes v) n) (fresh : Term) (ha : ∀ t ∈ inp.dataTys, Avail L t) :
    Sound (fun _ => True) (inp.validT L fresh) := by
  have nm := fun t (ht : t ∈ inp.dataTys) x => sound_lacksData (o := namesT L fresh t x) (ha t ht)
    fun hh he _ => namesT_isSome fresh t hh he x
  cases inp with
  | command i caller input =>
    exact sound_bind (nm v.caller (by simp [SymInput.dataTys]) caller) fun _ _ =>
      sound_bind (nm (v.commands.get i).input (by simp [SymInput.dataTys]) input) fun _ _ => trivial
  | query | clock | unmatched => trivial
  | answer k j to value | event i value => exact sound_mono (nm _ (by simp [SymInput.dataTys]) value) fun _ _ => trivial

theorem wfIn_sound (inp : SymInput v shs n) (ha : ∀ t ∈ inp.dataTys, Avail L t) :
    Sound (fun c => inp.wf L = some c) (need (lacksDatas inp.dataTys) (inp.wf L)) :=
  sound_lacksDatas ha fun h => inputWf_isSome inp h

end

theorem sound_error {α : Type} {p : α → Prop} {x : Except Refusal α} {r : Refusal} (h : Sound p x) (hx : x = .error r) :
    r.gap = false := by
  subst hx; exact h

section
variable {c : CheckedSpec} {v : ServiceV} (hv : v ∈ c.spec.services) (T : List TypeDecl)
  (senv : StepEnv (Layout.ofService c.program.defs v) (shapes v))
include hv

theorem unrollKind_gap (S : SymState v) (shown : List (Term × Term)) (sel : Term) (inp : SymInput v (shapes v) senv.nT) (ha : KindAvail c v inp)
    {x : SymInput v (shapes v) senv.nT × Refusal}
    (h : unrollKind (Layout.ofService c.program.defs v) T c.P v senv S shown sel inp = .error x) : x.2.gap = false := by
  unfold unrollKind at h
  cases h1 : encodeStep (Layout.ofService c.program.defs v) T c.P v senv S inp with
  | error r => simp only [h1] at h; cases h; exact sound_error (encodeStep_ofService hv T senv S inp) h1
  | ok t =>
    cases h2 : inp.validT (Layout.ofService c.program.defs v) S.fresh with
    | error r => simp only [h1, h2] at h; cases h; exact sound_error (validT_sound inp S.fresh ha.2) h2
    | ok valid =>
      cases h3 : need (lacksDatas inp.dataTys) (inp.wf (Layout.ofService c.program.defs v)) with
      | error r => simp only [h1, h2, h3] at h; cases h; exact sound_error (wfIn_sound inp ha.2) h3
      | ok wf => simp only [h1, h2, h3] at h; cases h

theorem unrollOne_gap (S : SymState v) (shown : List (Term × Term)) (i b : Nat) (f : Option Nat) :
    ∀ p ∈ (unrollOne (Layout.ofService c.program.defs v) T c.P v senv S shown i b f).2.2.2.1, p.2.gap = false := by
  intro p hp
  simp only [unrollOne, List.mem_filterMap, List.mem_map, List.mem_filter] at hp
  obtain ⟨r, ⟨inp, ⟨hinp, -⟩, rfl⟩, hr⟩ := hp
  split at hr
  · rename_i x hx; cases hr
    obtain ⟨k, hk, b', rfl⟩ := mem_placeKinds _ _ inp hinp
    exact unrollKind_gap hv T senv S shown _ _ (unrollKinds_avail c v k hk b') hx
  · cases hr

omit hv in
theorem unrollOne_avail (S : SymState v) (shown : List (Term × Term)) (i b : Nat) (f : Option Nat) :
    ∀ t ∈ (unrollOne (Layout.ofService c.program.defs v) T c.P v senv S shown i b f).1, Avail (Layout.ofService c.program.defs v) t := by
  intro t ht
  simp only [unrollOne, List.mem_append, List.mem_singleton, List.mem_flatMap] at ht
  rcases ht with rfl | ⟨inp, hinp, ht⟩
  · exact avail_int
  · obtain ⟨k, hk, b', rfl⟩ := mem_placeKinds _ _ inp hinp
    exact (unrollKinds_avail c v k hk b').1 t ht

theorem unrollSteps_gap : (S : SymState v) → (shown : List (Term × Term)) → (i b : Nat) → (fs : List (Option Nat)) →
    (∀ p ∈ (unrollSteps (Layout.ofService c.program.defs v) T c.P v senv S shown i b fs).2.2.2, p.2.gap = false) ∧
      ∀ t ∈ (unrollSteps (Layout.ofService c.program.defs v) T c.P v senv S shown i b fs).1,
        Avail (Layout.ofService c.program.defs v) t
  | _, _, _, _, [] => ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | S, shown, i, b, f :: fs => by
    have ih := unrollSteps_gap (unrollOne (Layout.ofService c.program.defs v) T c.P v senv S shown i b f).2.2.1.after
      (shown ++ (unrollOne (Layout.ofService c.program.defs v) T c.P v senv S shown i b f).2.2.1.shows) (i + 1)
      (unrollOne (Layout.ofService c.program.defs v) T c.P v senv S shown i b f).2.2.2.2 fs
    refine ⟨fun p hp => ?_, fun t ht => ?_⟩
    · simp only [unrollSteps, List.mem_append] at hp
      rcases hp with hp | hp
      · exact unrollOne_gap hv T senv S shown i b f p hp
      · exact ih.1 p hp
    · simp only [unrollSteps, List.mem_append] at ht
      rcases ht with ht | ht
      · exact unrollOne_avail T senv S shown i b f t ht
      · exact ih.2 t ht

/-- In each service's layout, the unrolled run never refuses with a layout gap, nor does any input kind it leaves out:
every refusal is the spec's (initial records past the slots, a limit, a string outside SMT-LIB's, a case the types
rule out). -/
theorem unrollBase_ofService (fs : List (Option Nat)) :
    Sound (fun B => ∀ p ∈ B.refused, p.2.gap = false)
      (unrollBase (Layout.ofService c.program.defs v) T c.P v senv fs) := by
  unfold unrollBase
  refine sound_bind (sound_need fun h0 => ?_) fun S0 _ => ?_
  · split
    · rename_i he; have := initState_ofService c hv he; simp [h0] at this
    · rfl
  obtain ⟨dts, hdts⟩ := datatypes_ofParts c.program.defs.parts v
  refine sound_bind_ok (need_ok.2 hdts) ?_
  have hu := unrollSteps_gap hv T senv S0 [] 0 0 fs
  exact sound_bind (sound_mapM _ fun t ht => sound_mono (sound_srt (hu.2 t ht)) fun _ _ => trivial)
    fun _ _ => hu.1

end

theorem stateTys_avail (c : CheckedSpec) (v : ServiceV) :
    ∀ t ∈ stateTys v (shapes v), Avail (Layout.ofService c.program.defs v) t := by
  intro t ht
  simp only [stateTys, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ht
  rcases ht with (rfl | rfl | rfl | rfl | rfl) | ⟨m, hm, rfl⟩
  · exact avail_stepTy c v (by simp [stepTys])
  · exact avail_int
  · exact avail_int
  · exact avail_int
  · exact avail_stepTy c v (by simp [stepTys])
  · exact avail_stepTy c v (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hm)))

section
variable {L : Layout} {r e : Ty}

theorem namesMachinesT_isSome (n : Term) : (ms : List (MachineV r e)) → (∀ m ∈ ms, L.Has m.table ∧ m.table.embeddable = true) →
    (xs : PerMachine (fun _ => Term) ms) → (namesMachinesT L n ms xs).isSome = true
  | [], _, .nil => rfl
  | m :: ms, h, .cons x xs => by
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (namesT_isSome n m.table (h m (by simp)).1 (h m (by simp)).2 x)
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (namesMachinesT_isSome n ms (fun m' hm' => h m' (by simp [hm'])) xs)
    simp [namesMachinesT, hc, hd]

end

section
variable {c : CheckedSpec} {v : ServiceV} (hv : v ∈ c.spec.services) (T : List TypeDecl)
  (senv : StepEnv (Layout.ofService c.program.defs v) (shapes v))
include hv

/-- In each service's layout, what prove's questions about an input kind share never refuses with a layout gap. -/
theorem stepAsk_ofService (inp : SymInput v (shapes v) senv.nT)
    (hinp : inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v)) :
    Sound (fun _ => True) (stepAsk (Layout.ofService c.program.defs v) T c.P v senv inp) := by
  have h := serviceGot_ofService hv
  have chk := c.checked v hv
  have ha := stepInputs_avail c v inp hinp
  unfold stepAsk
  refine sound_bind (encodeStep_ofService hv T senv _ inp) fun t _ => ?_
  refine sound_bind (sound_need fun hn => by
    have := wf_ofService c.program.defs chk (SymState.vars 0 : SymState v); rw [hn] at this; cases this) fun wf _ => ?_
  refine sound_bind (wfIn_sound inp ha.2) fun iwf _ => ?_
  obtain ⟨b, hb⟩ := pendingBelowT_ofService c.program.defs chk (SymState.vars 0 : SymState v).pending
    (SymState.vars 0 : SymState v).nextId
  refine sound_bind_ok hb ?_
  obtain ⟨⟨her, -⟩, hms, -, -, -⟩ := stateTys_iff.1 chk.stateTys
  have hs := stepTys_has c.program.defs chk
  refine sound_bind (sound_need fun hn => by
    obtain ⟨c1, h1⟩ := Option.isSome_iff_exists.1 (namesT_isSome (SymState.vars 0 : SymState v).fresh v.records
      (hs _ (by simp [stepTys])) her (SymState.vars 0 : SymState v).records)
    obtain ⟨c2, h2⟩ := Option.isSome_iff_exists.1 (namesMachinesT_isSome (SymState.vars 0 : SymState v).fresh v.machines
      (fun m hm => ⟨hs _ (by simp only [stepTys]; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hm))),
        (hms m hm).1⟩) (SymState.vars 0 : SymState v).machines)
    simp [namesStateT, h1, h2] at hn) fun _ _ => ?_
  refine sound_bind (shapesT_sound h.sorted v.machines (fun m hm => (h.machines m hm).1) _ _) fun _ _ => ?_
  refine sound_bind h.invariants fun ⟨inv, ci0⟩ hinv => ?_
  refine sound_bind (encodeInvariants_sound h.sorted hinv (avail_of_got h.records) h.rules _) fun ⟨rules, ci⟩ _ => ?_
  refine sound_bind (encodeInstChecks_sound h.sorted T v.machines (fun m hm => (h.machines m hm).1) _ _ _)
    fun ⟨checks, ck⟩ _ => ?_
  refine sound_bind (sound_mapM _ fun ty hty => sound_mono (sound_srt (by
    rcases List.mem_append.1 hty with hty | hty
    · exact stateTys_avail c v ty hty
    · exact ha.1 ty hty)) fun _ _ => trivial) fun vars _ => ?_
  obtain ⟨dts, hdts⟩ := datatypes_ofParts c.program.defs.parts v
  exact sound_bind_ok (need_ok.2 hdts) trivial

/-- In each service's layout, prove's questions about an input kind never refuse with a layout gap. -/
theorem questions_ofService (inp : SymInput v (shapes v) senv.nT)
    (hinp : inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v)) :
    Sound (fun _ => True) (questions (Layout.ofService c.program.defs v) T c.P v senv inp) :=
  sound_bind (stepAsk_ofService hv T senv inp hinp) fun _ _ => trivial

end

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {r e : Ty}

/-- A timer machine's two questions never refuse with a layout gap in a layout that has its datatypes and codes. -/
theorem timerQuestions_sound (hL : SortedLayout L) {m : MachineV r e} (hm : MachineGot L m)
    (hc : MachineCodes L P ds H m) (hdts : ∃ dts, L.datatypes? = some dts) :
    Sound (fun _ => True) (timerQuestions L m) := by
  unfold timerQuestions encodeTimer
  refine sound_bind (p := fun _ => True) (sound_bind hc.timer fun ⟨tc, c0⟩ htc => ?_) fun _ _ => ?_
  · refine sound_bind (findE_sound hL (avail_of_got hm.timer) has_find) fun _ _ => ?_
    refine sound_bind (findE_sound hL (avail_of_got hm.timerOne) has_find) fun _ _ => ?_
    refine sound_bind (adtCtor_sound hm.tctx _ _) fun _ _ => ?_
    refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ hm.tctx) fun c1 h1 => ?_
    refine sound_bind (apply_sound htc ⟨h1, trivial⟩ (avail_of_got hm.timer)) fun _ _ => ?_
    refine sound_bind (dataTermE_sound _) fun _ _ => ?_
    refine sound_bind (adtCtor_sound hm.tctx _ _) fun _ _ => ?_
    refine sound_bind (ofDataE_sound (P := P) (ds := ds) (H := H) _ hm.tctx) fun c2 h2 => ?_
    refine sound_bind (apply_sound htc ⟨h2, trivial⟩ (avail_of_got hm.timer)) fun _ _ => ?_
    exact sound_bind (dataTermE_sound _) fun _ _ => trivial
  · have ha : ∀ t ∈ timerTys m, Avail L t := by
      intro t ht
      simp only [timerTys, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact avail_of_got hm.key
      · exact avail_of_got hm.entry
      · exact hm.records
    refine sound_bind (sound_mapM _ fun x hx => sound_mono (sound_lacksData (ha x.1 (List.fst_mem_of_mem_zipIdx hx))
      fun hh he hk => wfT_isSome x.1 hh he hk _) fun _ _ => trivial) fun _ _ => ?_
    refine sound_bind (sound_mapM _ fun t ht => sound_mono (sound_srt (ha t ht)) fun _ _ => trivial) fun _ _ => ?_
    obtain ⟨dts, hd⟩ := hdts
    exact sound_bind_ok (need_ok.2 hd) trivial

end

/-- A lookup refused as `lacksDatas ts` is no gap where it finds a term for values of types that all have one. -/
theorem sound_lacksDatas_of {α : Type} {ts : List Ty} {o : Option α}
    (hf : (∀ t ∈ ts, t.embeddable = true ∧ t.plainKeys = true) → o.isSome = true) :
    Sound (fun a => o = some a) (need (lacksDatas ts) o) :=
  sound_need fun ho => by
    unfold lacksDatas
    split
    · rename_i t ht
      have hb := List.find?_some ht
      unfold lacksData
      split
      · rfl
      · split
        · rfl
        · rename_i he hk; simp_all
    · rename_i hn
      have := hf fun t ht => by
        have hb := List.find?_eq_none.1 hn t ht
        simp only [Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
        have he : t.embeddable = true := by
          cases h : t.embeddable
          · simp [h] at hb
          · rfl
        exact ⟨he, by simpa [he] using hb⟩
      simp [ho] at this

theorem hasWiths_of_mem {L : Layout} {D : Dsl → List Ty → Prop} : {vs : List (List Ty)} → Layout.HasWithss L D vs →
    ∀ fs ∈ vs, Layout.HasWiths L D fs
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, h⟩, fs, .tail _ hf => hasWiths_of_mem h fs hf

section
variable {L : Layout} {P : List AnySite} {ds : List (String × DeclaredV)} {H : List HandleSite} {r e : Ty}

theorem tablesEqT_sound (hL : SortedLayout L) : (ms : List (MachineV r e)) → (∀ m ∈ ms, Avail L m.table) →
    (xs ys : PerMachine (fun _ => Term) ms) → Sound (fun _ => True) (tablesEqT L ms xs ys)
  | [], _, .nil, .nil => trivial
  | m :: ms, h, .cons x xs, .cons y ys => by
    simp only [tablesEqT]
    exact sound_bind (eqFn_sound hL m.table (h m (by simp))) fun _ _ =>
      sound_bind (tablesEqT_sound hL ms (fun m' hm' => h m' (by simp [hm'])) xs ys) fun _ _ => trivial

end

section
variable {c : CheckedSpec} {v : ServiceV} (hv : v ∈ c.spec.services) (T : List TypeDecl)
  (senv : StepEnv (Layout.ofService c.program.defs v) (shapes v))
include hv

/-- In each service's layout, a pair of own kinds' two questions never refuse with a layout gap. -/
theorem pairQuestions_ofService (k1 k2 : OwnPlace (Layout.ofService c.program.defs v) v.event) :
    Sound (fun _ => True) (pairQuestions (Layout.ofService c.program.defs v) T c.P v senv k1 k2) := by
  have h := serviceGot_ofService hv
  have chk := c.checked v hv
  have hL := h.sorted
  obtain ⟨⟨her, -⟩, hms, -, -, -⟩ := stateTys_iff.1 chk.stateTys
  have hs := stepTys_has c.program.defs chk
  have heff : (Layout.ofService c.program.defs v).Has (.dsl .effect [v.event]) :=
    (hs (Ty.option (.dsl .effect [v.event])) (by simp [stepTys])).1.1.1
  have hown : ∀ k : OwnPlace (Layout.ofService c.program.defs v) v.event, ∀ t ∈ ((Layout.ofService c.program.defs v).ownsOf v.event)[k].fields,
      Layout.HasWith (Layout.ofService c.program.defs v) (fun _ _ => True) t := fun k t ht =>
    hasWiths_mem (hasWiths_of_mem heff.1 _ (List.mem_append_right _ (List.mem_map_of_mem (List.getElem_mem _)))) t ht
  have hwf : ∀ (k : OwnPlace (Layout.ofService c.program.defs v) v.event) z,
      Sound (fun a => ownWf (Layout.ofService c.program.defs v) v.event senv.dE k z = some a)
        (need (lacksDatas ((Layout.ofService c.program.defs v).ownsOf v.event)[k].fields)
          (ownWf (Layout.ofService c.program.defs v) v.event senv.dE k z)) := fun k z =>
    sound_lacksDatas_of fun hf => by
      simp only [ownWf, Option.isSome_map]
      exact mapM_some_of fun x hx => wfT_isSome x.1 (hown k x.1 (List.fst_mem_of_mem_zipIdx hx))
        (hf x.1 (List.fst_mem_of_mem_zipIdx hx)).1 (hf x.1 (List.fst_mem_of_mem_zipIdx hx)).2 _
  unfold pairQuestions encodePair
  refine sound_bind (p := fun _ => True) (sound_bind h.apply fun ⟨apply, ca⟩ happ => ?_) fun o _ => ?_
  · have step := fun records fresh n q eff xs (k : OwnPlace (Layout.ofService c.program.defs v) v.event) j =>
      encodeOwnKind_sound h T senv ((Layout.ofService c.program.defs v).effectsOf v.event).length happ records
        (SymState.vars 0 : SymState v).now fresh n q eff xs j
        (List.getElem_mem (l := (Layout.ofService c.program.defs v).ownsOf v.event) k.2)
    refine sound_bind (step _ _ _ _ _ _ k1 _) fun ⟨⟨_, a1⟩, c1, x1⟩ _ => ?_
    refine sound_bind (step _ _ _ _ _ _ k2 _) fun ⟨⟨_, a2⟩, c2, x2⟩ _ => ?_
    refine sound_bind (step _ _ _ _ _ _ k2 _) fun ⟨⟨_, b1⟩, c3, x3⟩ _ => ?_
    refine sound_bind (step _ _ _ _ _ _ k1 _) fun ⟨⟨_, b2⟩, c4, x4⟩ _ => ?_
    refine sound_bind (eqFn_sound hL v.records (avail_of_got h.records)) fun _ _ => ?_
    exact sound_bind (tablesEqT_sound hL v.machines (fun m hm => avail_of_got (h.machines m hm).1.1.table) _ _)
      fun _ _ => trivial
  refine sound_bind (sound_need fun hn => by
    have := wf_ofService c.program.defs chk (SymState.vars 0 : SymState v); rw [hn] at this; cases this) fun _ _ => ?_
  obtain ⟨b, hb⟩ := pendingBelowT_ofService c.program.defs chk (SymState.vars 0 : SymState v).pending
    (SymState.vars 0 : SymState v).nextId
  refine sound_bind_ok hb ?_
  refine sound_bind (sound_need fun hn => by
    obtain ⟨c1, h1⟩ := Option.isSome_iff_exists.1 (namesT_isSome (SymState.vars 0 : SymState v).fresh v.records
      (hs _ (by simp [stepTys])) her (SymState.vars 0 : SymState v).records)
    obtain ⟨c2, h2⟩ := Option.isSome_iff_exists.1 (namesMachinesT_isSome (SymState.vars 0 : SymState v).fresh v.machines
      (fun m hm => ⟨hs _ (by simp only [stepTys]; exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hm))),
        (hms m hm).1⟩) (SymState.vars 0 : SymState v).machines)
    simp [namesStateT, h1, h2] at hn) fun _ _ => ?_
  refine sound_bind (hwf k1 _) fun _ _ => ?_
  refine sound_bind (hwf k2 _) fun _ _ => ?_
  refine sound_bind (sound_mapM _ fun ty hty => sound_mono (sound_srt (by
    simp only [pairTys, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hty
    rcases hty with hty | rfl | rfl
    · exact stateTys_avail c v ty hty
    · exact fun _ => heff
    · exact fun _ => heff)) fun _ _ => trivial) fun _ _ => ?_
  obtain ⟨dts, hdts⟩ := datatypes_ofParts c.program.defs.parts v
  exact sound_bind_ok (need_ok.2 hdts) trivial

/-- In each service's layout, a timer machine's two questions never refuse with a layout gap. -/
theorem timerQuestions_ofService {m : MachineV v.records v.event} (hm : m ∈ v.machines) :
    Sound (fun _ => True) (timerQuestions (Layout.ofService c.program.defs v) m) :=
  have h := serviceGot_ofService hv
  timerQuestions_sound h.sorted (h.machines m hm).1.1 (h.machines m hm).1.2 (datatypes_ofParts c.program.defs.parts v)

end

/-- A builder's refusal once its theorem rules out a layout gap: the spec's, or a case the loaded program's types rule
out. -/
inductive Refused where
  /-- A construct of the spec the fragment leaves out. -/
  | spec (l : Limit)
  | unexpected (u : Unexpected)

/-- A refusal that is no layout gap, as the commands read it. -/
def Refusal.refused : (r : Refusal) → r.gap = false → Refused
  | .limit l, _ => .spec l
  | .unexpected u, _ => .unexpected u
  | .layout _, h => absurd h (by simp [Refusal.gap])

/-- A builder's result with its no-gap theorem: the value with what the theorem says of it, or the refusal, which is no
gap. The commands read builders only through this, so each builder they call has its theorem. -/
def Sound.get {α : Type} {p : α → Prop} : (x : Except Refusal α) → Sound p x → Except Refused {a // p a}
  | .ok a, h => .ok ⟨a, h⟩
  | .error r, h => .error (r.refused h)

end Tazuna.Smt
