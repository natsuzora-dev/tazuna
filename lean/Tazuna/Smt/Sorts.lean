import Tazuna.Smt.Pair
import Tazuna.Smt.Cover
import Tazuna.Smt.Timer
import Tazuna.Smt.NoGap

/-! Every sort a script declares holds a value, so `Unsat`'s premise is never free: a sort with no value would make
every question over it unsat whatever it asked. A script declares its variables at `Layout.srt?` of their types and
its datatypes from `Layout.datatypes?`; where both are found, every data
type's sort holds a value of `Sorted` (`sorted_exists`) and every effect type's a value of `EffSorted`
(`varSorted_exists`): a constructor whose fields' sorts are found too, or a collection whose slots are all free.
`sorts_inhabited` gives the `sorts` field of `Unsat` for the scripts of each question family: an input kind's step and
bound questions (`questions`), a pair of own kinds' (`pairQuestions`) and a timer machine's (`timerQuestions`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout}

theorem datatype_of_find {dts : List Datatype} (hd : L.datatypes? = some dts) {t : Ty} {x : Nat × Nat}
    (h : L.find? t = some x) : (L.datatype? (t, x.2)).isSome = true := by
  simp only [Layout.find?, Option.map_eq_some_iff] at h
  obtain ⟨⟨⟨u, m⟩, j⟩, hfind, rfl⟩ := h
  have hu := eq_of_same (by simpa using List.find?_some hfind)
  subst hu
  have hall := mapM_isSome L.datatype? L.types
  rw [show L.types.mapM L.datatype? = L.datatypes? from rfl, hd] at hall
  exact List.all_eq_true.1 hall.symm _ (List.fst_mem_of_mem_zipIdx (List.mem_of_find?_eq_some hfind))

theorem srt_found {t : Ty} (h : (L.srt? t).isSome = true) (hp : ∀ u, t ≠ .dsl .fresh u) (hi : t ≠ .int)
    (hdt : t ≠ .date) (hs : t ≠ .str) (hb : ∀ a vs, t ≠ .adt 0 a vs) : ∃ x, L.find? t = some x := by
  unfold Layout.srt? at h
  split at h <;> first
    | (exfalso; first | exact hi rfl | exact hdt rfl | exact hs rfl | exact hp _ rfl | exact hb _ _ rfl)
    | exact Option.isSome_iff_exists.1 (by simpa using h)

theorem mapM_some_mem {α β : Type} {f : α → Option β} {xs : List α} (h : (xs.mapM f).isSome = true) :
    ∀ x ∈ xs, (f x).isSome = true := by
  rw [mapM_isSome] at h; exact List.all_eq_true.1 h

theorem slotsView_free (dt : Nat) (zs : List Val) : (n : Nat) →
    slotsView dt zs.length (List.replicate n (.ctor dt 0 (.bool false :: zs))) = some (List.replicate n (false, zs))
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, slotsView, slotsView_free dt zs n]

/-- A collection value whose `n` slots are all free. -/
theorem collView_free (d dt n : Nat) (zs : List Val) :
    collView d dt n zs.length (.ctor d 0 (List.replicate n (.ctor dt 0 (.bool false :: zs)))) =
      some (List.replicate n (false, zs)) := by
  simp [collView, slotsView_free]

theorem free_occupied {zs : List Val} {n : Nat} {p : Bool × List Val} (hp : p ∈ List.replicate n (false, zs))
    (h : p.1 = true) : False := by
  rw [(List.eq_of_mem_replicate hp)] at h
  cases h

variable {dts : List Datatype}

mutual
/-- A data type whose sort a script can declare holds a value of that sort. -/
theorem sorted_exists (hd : L.datatypes? = some dts) : (t : Ty) → (L.srt? t).isSome = true → t.isData = true →
    ∃ w, Sorted L t w
  | .int, _, _ | .date, _, _ => ⟨.int 0, 0, rfl⟩
  | .str, _, _ => ⟨.str "", "", rfl, rfl⟩
  | .dsl k a, _, hx => by
    obtain rfl := sorted_dsl_data hx
    exact ⟨.int 0, 0, rfl⟩
  | .id, hs, _ => by
    obtain ⟨⟨d, n⟩, hf⟩ := srt_found hs (by simp) (by simp) (by simp) (by simp) (by simp)
    exact ⟨.ctor d 1 [.str ""], d, n, hf, .inr ⟨"", rfl, rfl⟩⟩
  | .adt 0 a vs, hs, _ => by
    simp only [Layout.srt?] at hs
    split at hs
    · rename_i hb
      obtain ⟨⟨rfl⟩, -⟩ := Option.isSome_iff_exists.1 hb
      exact ⟨.bool false, rfl, false, rfl⟩
    · cases hs
  | .adt (i + 1) a [], hs, _ => by
    obtain ⟨⟨d, n⟩, hf⟩ := srt_found hs (by simp) (by simp) (by simp) (by simp) (by simp)
    exact ⟨.ctor d 0 [], d, n, hf, rfl, rfl⟩
  | .adt (i + 1) a (fs :: rest), hs, hx => by
    obtain ⟨⟨d, n⟩, hf⟩ := srt_found hs (by simp) (by simp) (by simp) (by simp) (by simp)
    have hdt := datatype_of_find hd hf
    simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, List.mapM_cons, Option.isSome_bind] at hdt
    simp only [Ty.isData, Ty.isDatass, Bool.and_eq_true] at hx
    obtain ⟨ws, hws⟩ := sortedVs_exists hd fs (mapM_some_mem (Option.isSome_of_isSome_bind hdt)) hx.1
    exact ⟨.ctor d 0 ws, d, n, hf, 0, ws, rfl, .inl ⟨rfl, hws⟩⟩
  | .tuple ts, hs, hx => by
    obtain ⟨⟨d, n⟩, hf⟩ := srt_found hs (by simp) (by simp) (by simp) (by simp) (by simp)
    have hdt := datatype_of_find hd hf
    simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.isSome_bind] at hdt
    obtain ⟨ws, hws⟩ := sortedVs_exists hd ts (mapM_some_mem (by simpa using hdt)) (by simpa [Ty.isData] using hx)
    exact ⟨.ctor d 0 ws, d, n, ws, hf, rfl, hws⟩
  | .bag t, hs, _ => by
    obtain ⟨⟨d, n⟩, hf⟩ := srt_found hs (by simp) (by simp) (by simp) (by simp) (by simp)
    have hdt := datatype_of_find hd hf
    simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.isSome_bind] at hdt
    obtain ⟨⟨dt, m⟩, hft⟩ := srt_found (t := .tuple [Ty.bool, t]) (by simpa using hdt) (by simp) (by simp) (by simp)
      (by simp) (by simp)
    exact ⟨_, d, n, dt, m, _, hf, hft, collView_free d dt n [.int 0], fun _ hp h => (free_occupied hp h).elim⟩
  | .list t, hs, _ => by
    obtain ⟨⟨d, n⟩, hf⟩ := srt_found hs (by simp) (by simp) (by simp) (by simp) (by simp)
    have hdt := datatype_of_find hd hf
    simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.isSome_bind] at hdt
    obtain ⟨⟨dt, m⟩, hft⟩ := srt_found (t := .tuple [Ty.bool, t]) (by simpa using hdt) (by simp) (by simp) (by simp)
      (by simp) (by simp)
    exact ⟨_, d, n, dt, m, _, hf, hft, collView_free d dt n [.int 0], fun _ hp h => (free_occupied hp h).elim⟩
  | .table k v, hs, _ => by
    obtain ⟨⟨d, n⟩, hf⟩ := srt_found hs (by simp) (by simp) (by simp) (by simp) (by simp)
    have hdt := datatype_of_find hd hf
    simp only [Layout.datatype?, Option.pure_def, Option.bind_eq_bind, Option.isSome_bind] at hdt
    obtain ⟨⟨dt, m⟩, hft⟩ := srt_found (t := .tuple [Ty.bool, k, v]) (by simpa using hdt) (by simp) (by simp)
      (by simp) (by simp) (by simp)
    exact ⟨_, d, n, dt, m, _, hf, hft, collView_free d dt n [.int 0, .int 0], fun _ hp h => (free_occupied hp h).elim⟩
  | .fn .., hs, _ | .param _, hs, _ => by
    obtain ⟨x, hf⟩ := srt_found hs (by simp) (by simp) (by simp) (by simp) (by simp)
    have := datatype_of_find hd hf
    simp [Layout.datatype?] at this
theorem sortedVs_exists (hd : L.datatypes? = some dts) : (ts : List Ty) → (∀ t ∈ ts, (L.srt? t).isSome = true) →
    Ty.isDatas ts = true → ∃ ws, SortedVs L ts ws
  | [], _, _ => ⟨[], trivial⟩
  | t :: ts, hs, hx => by
    simp only [Ty.isDatas, Bool.and_eq_true] at hx
    obtain ⟨w, hw⟩ := sorted_exists hd t (hs t (by simp)) hx.1
    obtain ⟨ws, hws⟩ := sortedVs_exists hd ts (fun u hu => hs u (by simp [hu])) hx.2
    exact ⟨w :: ws, hw, hws⟩
end

/-- A data type's or an effect type's sort that a script can declare holds a value of the sort it declares. -/
theorem varSorted_exists (hL : SortedLayout L) (hd : L.datatypes? = some dts) {t : Ty} (hs : (L.srt? t).isSome = true)
    (ht : t.isData = true ∨ ∃ e, t = .dsl .effect [e]) : ∃ w, VarSorted L t w := by
  rcases ht with ht | ⟨e, rfl⟩
  · obtain ⟨w, hw⟩ := sorted_exists hd t hs ht
    exact ⟨w, varSorted_of_sorted hw⟩
  obtain ⟨⟨d, n⟩, hf⟩ := srt_found hs (by simp) (by simp) (by simp) (by simp) (by simp)
  have hdt := datatype_of_find hd hf
  cases hfs : L.effectFields e with
  | nil => exact ⟨.ctor d 0 [], d, n, 0, [], hf, rfl, .inr ⟨hfs, rfl, rfl⟩⟩
  | cons fs rest =>
    simp only [Layout.datatype?, hfs, Option.pure_def, Option.bind_eq_bind, List.mapM_cons] at hdt
    have hsrt := mapM_some_mem (Option.isSome_of_isSome_bind (Option.isSome_of_isSome_bind hdt))
    have hdata := (effectFields_sorted hL (e := e) (fs := fs) (by rw [hfs]; simp)).2
    obtain ⟨ws, hws⟩ := sortedVs_exists hd fs hsrt (by simpa [Ty.isData] using hdata)
    exact ⟨.ctor d 0 ws, d, n, 0, ws, hf, rfl, .inl ⟨fs, by simp [hfs], hws⟩⟩

/-- The sorts of a script's variables hold values wherever the script's declarations are found and each type is data
or an effect: `Unsat`'s `sorts`. -/
theorem sorts_inhabited (hL : SortedLayout L) (hd : L.datatypes? = some dts) {tys : List Ty} {vars : List Srt}
    (hv : tys.mapM L.srt? = some vars) (ht : ∀ t ∈ tys, t.isData = true ∨ ∃ e, t = .dsl .effect [e]) :
    SortsInhabited L tys := by
  have hs := mapM_some_mem (f := L.srt?) (xs := tys) (by simp [hv])
  have hw : ∀ n (h : n < tys.length), ∃ w, VarSorted L tys[n] w := fun n h =>
    varSorted_exists hL hd (hs _ (List.getElem_mem h)) (ht _ (List.getElem_mem h))
  refine ⟨{ coverModel [] with vars := fun n => if h : n < tys.length then (hw n h).choose else .bool false },
    fun n h => ?_⟩
  simp only [h, dite_true]
  exact (hw n h).choose_spec

theorem mapM_need {α : Type} {w : Ty → Refusal} {f : Ty → Option α} : {tys : List Ty} → {xs : List α} →
    tys.mapM (fun t => need (w t) (f t)) = .ok xs → tys.mapM f = some xs
  | [], xs, h => by simp only [List.mapM_nil] at h ⊢; cases pure_ok.1 h; rfl
  | t :: tys, xs, h => by
    simp only [List.mapM_cons] at h ⊢
    obtain ⟨x, hx, h⟩ := bind_ok.1 h
    obtain ⟨ys, hys, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    simp [need_ok.1 hx, mapM_need hys]

/-- The state's types are data. -/
theorem stateTys_data (v : ServiceV) : ∀ t ∈ stateTys v (shapes v), t.isData = true := by
  intro t ht
  simp only [stateTys, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at ht
  rcases ht with (rfl | rfl | rfl | rfl | rfl) | ⟨m, -, rfl⟩
  · exact v.records_data
  · rfl
  · rfl
  · rfl
  · simp [pendingTable, Ty.isData, pendingEntry_data]
  · exact m.table_data

/-- The types of the inputs a step question asks about are data: the answer shapes are those whose answers are. -/
theorem stepInputs_data {v : ServiceV} {shs : List (PendingShape v.event)} {n b : Nat} (hc : v.caller.isData = true)
    {inp : SymInput v shs n} (h : inp ∈ stepInputs v shs n b) :
    ∀ t ∈ inp.tys, t.isData = true := by
  simp only [stepInputs, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at h
  rcases h with ((⟨i, -, rfl⟩ | ⟨k, hk, j, -, rfl⟩) | ⟨i, -, rfl⟩) | rfl <;>
    simp only [SymInput.tys, List.mem_cons, List.not_mem_nil, or_false]
  · rintro t (rfl | rfl)
    · exact hc
    · exact CommandV.input_data _
  · simp only [answerShapes, List.mem_filter] at hk
    rintro t (rfl | rfl)
    · rfl
    · exact hk.2
  · rintro t rfl; exact SubscriptionV.event_data _
  · rintro t rfl; rfl

/-- The sorts of an input kind's step and bound questions hold values: the input's types are data. -/
theorem questions_sorts (hL : SortedLayout L) {T : List TypeDecl} {P : List AnySite} {v : ServiceV}
    {senv : StepEnv L (shapes v)} {inp : SymInput v (shapes v) senv.nT} {r}
    (hq : questions L T P v senv inp = .ok r) (hc : v.caller.isData = true)
    (hin : inp ∈ stepInputs v (shapes v) senv.nT (stateWidth v)) :
    SortsInhabited L (stateTys v (shapes v) ++ inp.tys) := by
  simp only [questions] at hq
  obtain ⟨a, ha, -⟩ := bind_ok.1 hq
  simp only [stepAsk] at ha
  obtain ⟨_, -, ha⟩ := bind_ok.1 ha
  obtain ⟨_, -, ha⟩ := bind_ok.1 ha
  obtain ⟨_, -, ha⟩ := bind_ok.1 ha
  obtain ⟨_, -, ha⟩ := bind_ok.1 ha
  obtain ⟨_, -, ha⟩ := bind_ok.1 ha
  obtain ⟨_, -, ha⟩ := bind_ok.1 ha
  obtain ⟨_, -, ha⟩ := bind_ok.1 ha
  obtain ⟨_, -, ha⟩ := bind_ok.1 ha
  obtain ⟨vars, hvars, ha⟩ := bind_ok.1 ha
  obtain ⟨dts, hdts, -⟩ := bind_ok.1 ha
  refine sorts_inhabited hL (need_ok.1 hdts) (mapM_need hvars) fun t ht => .inl ?_
  rcases List.mem_append.1 ht with ht | ht
  · exact stateTys_data v t ht
  · exact stepInputs_data hc hin t ht

/-- The sorts of a pair of own kinds' questions hold values: the state's, and the effect datatype's twice. -/
theorem pair_sorts (hL : SortedLayout L) {T : List TypeDecl} {P : List AnySite} {v : ServiceV}
    {senv : StepEnv L (shapes v)} {k1 k2 : OwnPlace L v.event} {r} (hq : pairQuestions L T P v senv k1 k2 = .ok r) :
    SortsInhabited L (pairTys v) := by
  simp only [pairQuestions] at hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨vars, hvars, hq⟩ := bind_ok.1 hq
  obtain ⟨dts, hdts, -⟩ := bind_ok.1 hq
  refine sorts_inhabited hL (need_ok.1 hdts) (mapM_need hvars) fun t ht => ?_
  simp only [pairTys, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | rfl | rfl
  · exact .inl (stateTys_data v t ht)
  · exact .inr ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

/-- The sorts of a timer machine's questions hold values: its key's, its state's, the records' and Int's. -/
theorem timer_sorts (hL : SortedLayout L) {r e : Ty} {m : MachineV r e} {x} (hq : timerQuestions L m = .ok x) :
    SortsInhabited L (timerTys m) := by
  simp only [timerQuestions] at hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨_, -, hq⟩ := bind_ok.1 hq
  obtain ⟨vars, hvars, hq⟩ := bind_ok.1 hq
  obtain ⟨dts, hdts, -⟩ := bind_ok.1 hq
  refine sorts_inhabited hL (need_ok.1 hdts) (mapM_need hvars) fun t ht => .inl ?_
  simp only [timerTys, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact m.key_data
  · exact m.state_data
  · exact m.records_data
  · rfl

end

end Tazuna.Smt
