import Tazuna.Smt.UnrollDecode

/-! Every run is a model of its unrolled script (`runs_covered`), the converse of `unroll_decode`. A run whose inputs
fit the slots, are valid, do not fault and whose steps stay within the slots gives a model: each step's selector holds
the input's kind (`Input.pick`), and each kind of the step holds the input's values where the kind is the input's
(`kindVals`). An answer's kinds all hold the answer's wire id, so the one slot that holds the request is the only case
that can hold, and the kinds whose shape answers with the answer's type all hold its value. The other constants hold
any value of their sort. So "no model within `d` steps" means no such run of `d` inputs. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {v : ServiceV}

/-- Whether the kind is the input's: the same command, query or subscription, a clock line, or an answer at a shape
whose answers have the answer's type. -/
def SymInput.isOf {shs : List (PendingShape v.event)} {n : Nat} (x : Input v) : SymInput v shs n → Bool
  | .command i _ _ => match x with | .command i' _ _ => i == i' | _ => false
  | .query i _ _ => match x with | .query i' _ _ => i == i' | _ => false
  | .answer k _ _ _ => match x with | .answer _ ⟨t, _⟩ => (Ty.same (answerTy shs[k].output shs[k].rejection) t).isSome | _ => false
  | .unmatched .. => false
  | .event i _ => match x with | .event i' _ => i == i' | _ => false
  | .clock _ => match x with | .clock _ => true | _ => false

variable (L : Layout)

/-- The values of the input's terms, where they fit the slots: `inputVals`, and a query's caller and input too, since
a query is a kind of an unrolled step. -/
def unrollVals (hc : v.caller.isData = true) : Input v → Option (List Val)
  | .query i caller input => (embedV L v.caller (Ty.up _ hc caller)).bind fun c =>
    (embedV L _ (Ty.up _ (v.queries.get i).input_data input)).map fun x => [c, x]
  | x => inputVals L hc x

/-- Some value of the type's sort, where one exists. -/
noncomputable def someVal (t : Ty) : Val :=
  open Classical in if h : ∃ w, Sorted L t w then h.choose else .bool false

/-- The values a kind's constants take in the model of a run whose step takes the input `x`: the input's where the
kind is the input's and they fit; for another answer kind, the answer's wire id and some value; else some value of each sort. -/
noncomputable def kindVals (hc : v.caller.isData = true) {n : Nat} (x : Input v) (inp : SymInput v (shapes v) n) :
    List Val :=
  match inp.isOf x, unrollVals L hc x with
  | true, some vs => vs
  | _, _ =>
    match inp, x with
    | .answer .., .answer to _ => .int (Int.ofNat to) :: (inp.tys.drop 1).map (someVal L)
    | _, _ => inp.tys.map (someVal L)

end

section
variable {M : Model} {L : Layout} {v : ServiceV}

/-- Where an answer kind's case holds, the request its wire id names is pending, as a request of the kind's shape. -/
theorem hit_find (s : State v) {shs : List (PendingShape v.event)} {to : Nat} {pending toT : Term}
    (hpend : PendingRel L shs (pending.denote M) s.pending) (hto : toT.denote M = .int (Int.ofNat to))
    (senv : StepEnv L shs) (k : Fin shs.length) (j : Fin senv.nT)
    (hhit : Holds M (Term.and (pendingSlotAt senv.dT senv.dtT j pending).flag
      (.and (.eq (pendingSlotAt senv.dT senv.dtT j pending).id toT)
        (.is senv.dP k (pendingSlotAt senv.dT senv.dtT j pending).entry)))) :
    ∃ p, s.pending.find? (·.id == to) = some p ∧ p.request.output = shs[k].output ∧
      p.request.rejection = shs[k].rejection := by
  obtain ⟨tbl, htbl, hlist⟩ := hpend
  have h3' := pendingSlot_at (d := senv.dT) (dt := senv.dtT) j.2 pending
  generalize pendingSlotAt senv.dT senv.dtT j pending = sl at h3' hhit
  obtain ⟨f, tk, te⟩ := sl
  obtain ⟨hhf, hhrest⟩ := (holds_and _ _).1 hhit
  obtain ⟨hheq, hhis⟩ := (holds_and _ _).1 hhrest
  obtain ⟨sv, ys, hS, -, -, hperm, hh⟩ := table_view (M := M) htbl senv.hT
  obtain ⟨b, hbsv, hfb⟩ := slot_at hS j h3'
  have hb : b = true := by simpa [Holds, hfb, Val.toBool] using hhf
  subst hb
  obtain ⟨y, hy, zk, zv, hxs, hzk, hzv⟩ := forall2_mem_right hh _ (by
    simp only [occupied, List.mem_filterMap]; exact ⟨_, hbsv, rfl⟩)
  simp only [Term.denotes, List.cons.injEq, and_true] at hxs
  obtain ⟨htk, hte⟩ := hxs
  have hkey : (y.1 : Nat) = to := by
    have e := Val.eq_of_beq _ _ (by simp only [Holds, Term.denote, Val.toBool] at hheq; exact hheq)
    change zk = Val.int (Int.ofNat y.1) at hzk
    rw [htk, hzk, hto] at e
    exact Int.ofNat.inj (Val.int.inj e)
  obtain ⟨d', n', hf', hra⟩ := hzv
  have hde := find_det hf' senv.hPE
  subst d'
  obtain ⟨j', sh', fx, vals, hj', hzv', -, hpo⟩ := relAlts_pending (L := L) to shs 0 y.2 zv hra
  have hjk : j' = k := by
    have := hhis
    simp only [Holds, Term.denote, hte, hzv', Val.toBool, beq_self_eq_true, Bool.true_and, beq_iff_eq] at this
    omega
  subst j'
  rw [List.getElem?_eq_getElem k.2] at hj'
  cases hj'
  refine ⟨shs[k].pending to fx, ?_, rfl, rfl⟩
  rw [find?_perm_ids hlist (pendingList_ids _ tbl.1 tbl.2)]
  change _ = some (shs[(k : Nat)].pending to fx)
  rw [← hpo, ← hkey]
  exact find_pending shs tbl.1 tbl.2 y (hperm.mem_iff.1 hy)

end

section
variable {v : ServiceV} {shs : List (PendingShape v.event)} {n : Nat}

/-- Each placed kind sits between the kinds placed before and after it, its terms the constants after theirs. -/
theorem placeKinds_split : (ks : List (Nat × (Nat → SymInput v shs n))) → (b : Nat) →
    (∀ p ∈ ks, ∀ c, (p.2 c).tys.length = p.1 ∧ (p.2 c).terms = (List.range p.1).map (fun i => .var (c + i))) →
    ∀ x ∈ (placeKinds ks b).1, ∃ pre post c, (placeKinds ks b).1 = pre ++ x :: post ∧
      c = b + (pre.flatMap SymInput.tys).length ∧ (∃ p ∈ ks, x = p.2 c)
  | [], b, _ => fun _ h => by cases h
  | (w, f) :: ks, b, hk => by
    have hf := hk (w, f) (by simp) b
    have ih := placeKinds_split ks (b + w) fun p hp => hk p (by simp [hp])
    intro x hm
    simp only [placeKinds, List.mem_cons] at hm ⊢
    rcases hm with rfl | hm
    · exact ⟨[], _, b, rfl, by simp, (w, f), by simp, rfl⟩
    · obtain ⟨pre, post, c, he, hc, p, hp, rfl⟩ := ih x hm
      refine ⟨f b :: pre, post, c, by rw [he]; rfl, ?_, p, by simp [hp], rfl⟩
      simp only [List.flatMap_cons, List.length_append, hf.1, hc]
      omega

/-- Every kind is placed. -/
theorem placeKinds_mem : (ks : List (Nat × (Nat → SymInput v shs n))) → (b : Nat) →
    ∀ p ∈ ks, ∃ c, p.2 c ∈ (placeKinds ks b).1
  | [], _ => fun _ h => by cases h
  | (w, f) :: ks, b => by
    intro p hp
    simp only [placeKinds, List.mem_cons] at hp ⊢
    rcases hp with rfl | hp
    · exact ⟨b, .inl rfl⟩
    · obtain ⟨c, hc⟩ := placeKinds_mem ks (b + w) p hp
      exact ⟨c, .inr hc⟩

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV}

/-- An answer that does not fault names a pending request whose answers have its type. -/
theorem answer_found {s : State v} {to : Nat} {t : Ty} {value : t.den0}
    (hno : ∀ f, (step T v s (.answer to ⟨t, value⟩)).outcome ≠ .fault f) :
    ∃ p, s.pending.find? (·.id == to) = some p ∧ t = answerTy p.request.output p.request.rejection := by
  cases hf : s.pending.find? (·.id == to) with
  | none => exact absurd (by simp only [step, hf]) (hno .answerUnmatched)
  | some p =>
    cases hsame : Ty.same t (answerTy p.request.output p.request.rejection) with
    | none => exact absurd (by simp only [step, hf, hsame]) (hno .answerUnmatched)
    | some e => exact ⟨p, rfl, e.down⟩

theorem pick_of_eq {b : Nat} {m n : Nat} (h : Holds M (.eq (.var b) (.int (n : Int)))) (hb : M.vars b = .int (m : Int)) :
    m = n := by
  have e := Val.eq_of_beq _ _ (by simp only [Holds, Term.denote, Val.toBool] at h; exact h)
  rw [hb] at e
  exact Int.ofNat.inj (Val.int.inj e)

variable (hc : v.caller.isData = true)

theorem kindVals_of {n : Nat} {x : Input v} {inp : SymInput v (shapes v) n} {vs : List Val} (hi : inp.isOf x = true)
    (hv : unrollVals L hc x = some vs) : kindVals L hc x inp = vs := by
  simp [kindVals, hi, hv]

/-- An answer kind's first constant holds the answer's wire id. -/
theorem kindVals_answer {n : Nat} {k : Fin (shapes v).length} {j : Fin n} {toT valT : Term} {to : Nat} {w : WireVal}
    (hv : (unrollVals L hc (.answer to w)).isSome = true) :
    (kindVals L hc (.answer to w) (.answer k j toT valT))[0]? = some (.int (Int.ofNat to)) := by
  obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.1 hv
  obtain ⟨t, value⟩ := w
  cases hi : (SymInput.answer (v := v) (shs := shapes v) k j toT valT).isOf (.answer to ⟨t, value⟩)
  · simp [kindVals, hi]
  · rw [kindVals_of hc hi hvs]
    simp only [unrollVals, inputVals] at hvs
    split at hvs
    · obtain ⟨w, -, rfl⟩ := map_some.1 hvs; rfl
    · cases hvs

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {P : List AnySite} {v : ServiceV} (hc : v.caller.isData = true)
  (senv : StepEnv L (shapes v))

/-- A kind a model's step picks is the input's: the selector holds the input's kind, which only that command, query,
subscription or clock line has, and an answer kind's case holds only at the slot that holds the request its wire id
names, a request whose answers have the answer's type where the step does not fault. -/
theorem isOf_of_picks {ans : Bool} {p : Nat × (Nat → SymInput v (shapes v) senv.nT)}
    (hp : p ∈ unrollKinds v (shapes v) senv.nT ans) (c : Nat) {S : SymState v} {s : State v}
    (hR : StateRel M L T (shapes v) S s) {x : Input v} (hno : ∀ f, (step T v s x).outcome ≠ .fault f)
    (hv : (unrollVals L hc x).isSome = true)
    (hvars : ∀ q (h : q < (kindVals L hc x (p.2 c)).length), M.vars (c + q) = (kindVals L hc x (p.2 c))[q])
    {b : Nat} (hb : M.vars b = .int (x.pick : Int)) {t : EncodedStep v}
    (ht : encodeStep L T P v senv S (p.2 c) = .ok t)
    (hpk : Holds M (selectsT (.var b) (p.2 c, t))) : (p.2 c).isOf x = true := by
  obtain ⟨hsel, hcase⟩ := (holds_andT _ _).1 hpk
  have he := pick_of_eq hsel hb
  simp only [unrollKinds, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (((⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | hp) | ⟨i, -, rfl⟩) | rfl
  · have := i.2
    cases x with
    | command i' => simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; simp [SymInput.isOf, Fin.ext_iff, he]
    | _ => simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
  · have := i.2
    cases x with
    | query i' => simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; simp [SymInput.isOf, Fin.ext_iff]; omega
    | command i' => have := i'.2; simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
    | _ => simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
  · split at hp
    · simp only [List.mem_flatMap, List.mem_map] at hp
      obtain ⟨k, -, j, -, rfl⟩ := hp
      cases x with
      | answer to w =>
        obtain ⟨ty, value⟩ := w
        rw [encodeStep_answer_case ht] at hcase
        have hk0 := kindVals_answer (k := k) (j := j) (toT := .var c) (valT := .var (c + 1)) hc hv
        have h0 := hvars 0 (List.getElem?_eq_some_iff.1 hk0).1
        simp only at h0
        rw [(List.getElem?_eq_some_iff.1 hk0).2, Nat.add_zero] at h0
        obtain ⟨p', hf, hout, hrej⟩ := hit_find s (to := to) hR.pending (by simp [Term.denote, h0]) senv k j hcase
        obtain ⟨p'', hf', hty⟩ := answer_found hno
        rw [hf] at hf'
        cases hf'
        simp only [SymInput.isOf]
        rw [hty, hout, hrej]
        exact Ty_same_self _
      | command i' => have := i'.2; simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
      | query i' => have := i'.2; simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
      | event i' => simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
      | clock => simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
    · cases hp
  · have := i.2
    cases x with
    | event i' => simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; simp [SymInput.isOf, Fin.ext_iff]; omega
    | command i' => have := i'.2; simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
    | query i' => have := i'.2; simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
    | _ => simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
  · cases x with
    | clock => rfl
    | command i' => have := i'.2; simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
    | query i' => have := i'.2; simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
    | event i' => have := i'.2; simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega
    | _ => simp only [Input.pick, SymInput.pick, Input.kind, SymInput.kind, PickKind.pick] at he; omega

end

section
variable {M : Model} {L : Layout} {v : ServiceV} (hc : v.caller.isData = true)

/-- A kind that is the input's, whose constants hold the input's values, decodes to the input. -/
theorem decode_of_isOf {n : Nat} {ans : Bool} {p : Nat × (Nat → SymInput v (shapes v) n)}
    (hp : p ∈ unrollKinds v (shapes v) n ans) (c : Nat) {x : Input v} {vs : List Val}
    (hv : unrollVals L hc x = some vs)
    (hvars : ∀ q (h : q < (kindVals L hc x (p.2 c)).length), M.vars (c + q) = (kindVals L hc x (p.2 c))[q])
    (hi : (p.2 c).isOf x = true) : (p.2 c).decode M L hc = some x := by
  rw [kindVals_of hc hi hv] at hvars
  simp only [unrollKinds, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (((⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | hp) | ⟨i, -, rfl⟩) | rfl
  · cases x with
    | command i' caller input =>
      simp only [SymInput.isOf, beq_iff_eq] at hi
      subst hi
      obtain ⟨wc, hwc, h⟩ := bind_some.1 hv
      obtain ⟨wa, hwa, rfl⟩ := map_some.1 h
      have h0 := hvars 0 (by simp)
      have h1 := hvars 1 (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1
      simp [SymInput.decode, Term.denote, h0, h1, decode_embed _ _ _ hwc, Ty.down_up]
      exact ⟨_, decode_embed _ _ _ hwa, Ty.down_up _ _ _⟩
    | _ => simp [SymInput.isOf] at hi
  · cases x with
    | query i' caller input =>
      simp only [SymInput.isOf, beq_iff_eq] at hi
      subst hi
      obtain ⟨wc, hwc, h⟩ := bind_some.1 hv
      obtain ⟨wa, hwa, rfl⟩ := map_some.1 h
      have h0 := hvars 0 (by simp)
      have h1 := hvars 1 (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1
      simp [SymInput.decode, Term.denote, h0, h1, decode_embed _ _ _ hwc, Ty.down_up]
      exact ⟨_, decode_embed _ _ _ hwa, Ty.down_up _ _ _⟩
    | _ => simp [SymInput.isOf] at hi
  · split at hp
    · simp only [List.mem_flatMap, List.mem_map] at hp
      obtain ⟨k, -, j, -, rfl⟩ := hp
      cases x with
      | answer to w =>
        obtain ⟨t, value⟩ := w
        simp only [SymInput.isOf] at hi
        have heq := eq_of_same hi
        subst heq
        simp only [unrollVals, inputVals] at hv
        split at hv
        · rename_i htd
          obtain ⟨w, hw, rfl⟩ := map_some.1 hv
          have h0 := hvars 0 (by simp)
          have h1 := hvars 1 (by simp)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1
          simp [SymInput.decode, decodeAnswer, Term.denote, h0, h1, natOf]
          exact ⟨htd, _, decode_embed _ _ _ hw, Ty.down_up _ _ _⟩
        · cases hv
      | _ => simp [SymInput.isOf] at hi
    · cases hp
  · cases x with
    | event i' value =>
      simp only [SymInput.isOf, beq_iff_eq] at hi
      subst hi
      obtain ⟨w, hw, rfl⟩ := map_some.1 hv
      have h0 := hvars 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at h0
      simp [SymInput.decode, Term.denote, h0]
      exact ⟨_, decode_embed _ _ _ hw, Ty.down_up _ _ _⟩
    | _ => simp [SymInput.isOf] at hi
  · cases x with
    | clock time =>
      cases hv
      have h0 := hvars 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at h0
      simp [SymInput.decode, Term.denote, h0, intOf]
    | _ => simp [SymInput.isOf] at hi

end

section
variable {L : Layout} {v : ServiceV} (hc : v.caller.isData = true)

/-- A value of the type's sort, wherever the sort holds one. -/
def SortedIf (L : Layout) (t : Ty) (w : Val) : Prop := (∃ w', Sorted L t w') → Sorted L t w

theorem someVal_sorted (t : Ty) : SortedIf L t (someVal L t) := fun h => by
  simp only [someVal, h, dite_true]; exact h.choose_spec

theorem someVals_sorted : (ts : List Ty) → Forall2 (SortedIf L) ts (ts.map (someVal L))
  | [] => trivial
  | t :: ts => ⟨someVal_sorted t, someVals_sorted ts⟩

/-- A kind's values are one per constant, each of the constant's sort wherever the sort holds one. -/
theorem kindVals_sorted {n : Nat} {ans : Bool} {p : Nat × (Nat → SymInput v (shapes v) n)}
    (hp : p ∈ unrollKinds v (shapes v) n ans) (c : Nat) (x : Input v) :
    Forall2 (SortedIf L) (p.2 c).tys (kindVals L hc x (p.2 c)) := by
  have hdflt : ∀ inp : SymInput v (shapes v) n, Forall2 (SortedIf L) inp.tys
      (match inp, x with
        | .answer .., .answer to _ => .int (Int.ofNat to) :: (inp.tys.drop 1).map (someVal L)
        | _, _ => inp.tys.map (someVal L)) := by
    intro inp
    cases inp <;> cases x <;> first
      | exact someVals_sorted _
      | exact ⟨fun _ => ⟨_, rfl⟩, someVals_sorted _⟩
  unfold kindVals
  split
  · rename_i vs hi hv
    simp only [unrollKinds, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (((⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | hp) | ⟨i, -, rfl⟩) | rfl
    · cases x with
      | command i' caller input =>
        simp only [SymInput.isOf, beq_iff_eq] at hi
        subst hi
        obtain ⟨wc, hwc, h⟩ := bind_some.1 hv
        obtain ⟨wa, hwa, rfl⟩ := map_some.1 h
        exact ⟨fun _ => sorted_of_embed hwc, fun _ => sorted_of_embed hwa, trivial⟩
      | _ => simp [SymInput.isOf] at hi
    · cases x with
      | query i' caller input =>
        simp only [SymInput.isOf, beq_iff_eq] at hi
        subst hi
        obtain ⟨wc, hwc, h⟩ := bind_some.1 hv
        obtain ⟨wa, hwa, rfl⟩ := map_some.1 h
        exact ⟨fun _ => sorted_of_embed hwc, fun _ => sorted_of_embed hwa, trivial⟩
      | _ => simp [SymInput.isOf] at hi
    · split at hp
      · simp only [List.mem_flatMap, List.mem_map] at hp
        obtain ⟨k, -, j, -, rfl⟩ := hp
        cases x with
        | answer to w =>
          obtain ⟨t, value⟩ := w
          simp only [SymInput.isOf] at hi
          have heq := eq_of_same hi
          subst heq
          simp only [unrollVals, inputVals] at hv
          split at hv
          · obtain ⟨w, hw, rfl⟩ := map_some.1 hv
            exact ⟨fun _ => ⟨_, rfl⟩, fun _ => sorted_of_embed hw, trivial⟩
          · cases hv
        | _ => simp [SymInput.isOf] at hi
      · cases hp
    · cases x with
      | event i' value =>
        simp only [SymInput.isOf, beq_iff_eq] at hi
        subst hi
        obtain ⟨w, hw, rfl⟩ := map_some.1 hv
        exact ⟨fun _ => sorted_of_embed hw, trivial⟩
      | _ => simp [SymInput.isOf] at hi
    · cases x with
      | clock time => cases hv; exact ⟨fun _ => ⟨_, rfl⟩, trivial⟩
      | _ => simp [SymInput.isOf] at hi
  · exact hdflt _

end

section
variable {M : Model} {L : Layout} {v : ServiceV} (hc : v.caller.isData = true)

theorem sorted_of_srt (hL : SortedLayout L) {t : Ty} (hs : (L.srt? t).isSome = true) : t.sorted = true := by
  unfold Layout.srt? at hs
  split at hs
  · rfl
  · rfl
  · simp [Ty.sorted]
  · rfl
  · rename_i vs
    split at hs
    · rename_i h; simpa [Ty.sorted] using h
    · cases hs
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (by simpa using hs)
    exact sorted_of_find hL hx

/-- A data type that has a sort is comparable. -/
theorem comparable_of_srt (hL : SortedLayout L) {t : Ty} (hs : (L.srt? t).isSome = true) (hd : t.isData = true) :
    t.comparable = true :=
  Ty.comparable_of_sorted t (sorted_of_srt hL hs) hd

theorem names_holds (hL : SortedLayout L) {fresh : Term} {N : Nat} (hn : fresh.denote M = .int (N : Int)) {t : Ty}
    (hs : (L.srt? t).isSome = true) (hd : t.isData = true) {x c : Term} (h : namesT L fresh t x = some c) {y : t.den0}
    {w : Val} (hw : embedV L t (Ty.up t hd y) = some w) (hx : x.denote M = w)
    (hy : ∀ P : PBij, P.Fixes N → Ty.rel0 P t y y) : Holds M c :=
  (names_rel0 hn (comparable_of_srt hL hs hd) h (hx ▸ embed_rel _ _ _ hw)).2 (hy _ (PBij.below_fixes N))

/-- A kind that is the input's, whose constants hold a valid input's values, holds its names term. -/
theorem valid_of_isOf (hL : SortedLayout L) {n : Nat} {ans : Bool} {p : Nat × (Nat → SymInput v (shapes v) n)}
    (hp : p ∈ unrollKinds v (shapes v) n ans) (c : Nat) {x : Input v} {vs : List Val}
    (hv : unrollVals L hc x = some vs)
    (hvars : ∀ q (h : q < (kindVals L hc x (p.2 c)).length), M.vars (c + q) = (kindVals L hc x (p.2 c))[q])
    (hi : (p.2 c).isOf x = true) (hsrt : ∀ t ∈ (p.2 c).tys, (L.srt? t).isSome = true) {s : State v}
    (hval : x.Valid s) {fresh : Term} (hn : fresh.denote M = .int (s.fresh : Int)) {valid : Term}
    (hvt : (p.2 c).validT L fresh = .ok valid) : Holds M valid := by
  rw [kindVals_of hc hi hv] at hvars
  simp only [unrollKinds, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (((⟨i, -, rfl⟩ | ⟨i, -, rfl⟩) | hp) | ⟨i, -, rfl⟩) | rfl
  · cases x with
    | command i' caller input =>
      simp only [SymInput.isOf, beq_iff_eq] at hi
      subst hi
      obtain ⟨wc, hwc, h⟩ := bind_some.1 hv
      obtain ⟨wa, hwa, rfl⟩ := map_some.1 h
      have h0 := hvars 0 (by simp)
      have h1 := hvars 1 (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1
      simp only [SymInput.validT] at hvt
      obtain ⟨cc, hcc, hvt⟩ := bind_ok.1 hvt
      obtain ⟨cx, hcx, hvt⟩ := bind_ok.1 hvt
      cases pure_ok.1 hvt
      simp only [SymInput.tys, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hsrt
      exact (holds_andT _ _).2
        ⟨names_holds hL hn hsrt.1 hc (need_ok.1 hcc) hwc (by simp [Term.denote, h0]) fun P hP => (hval P hP).1,
          names_holds hL hn hsrt.2 _ (need_ok.1 hcx) hwa (by simp [Term.denote, h1]) fun P hP => (hval P hP).2⟩
    | _ => simp [SymInput.isOf] at hi
  · cases pure_ok.1 hvt; exact holds_tt
  · split at hp
    · simp only [List.mem_flatMap, List.mem_map] at hp
      obtain ⟨k, -, j, -, rfl⟩ := hp
      cases x with
      | answer to w =>
        obtain ⟨t, value⟩ := w
        simp only [SymInput.isOf] at hi
        have heq := eq_of_same hi
        subst heq
        simp only [unrollVals, inputVals] at hv
        split at hv
        · rename_i htd
          obtain ⟨w, hw, rfl⟩ := map_some.1 hv
          have h1 := hvars 1 (by simp)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h1
          simp only [SymInput.validT] at hvt
          simp only [SymInput.tys, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hsrt
          exact names_holds hL hn hsrt.2 htd (need_ok.1 hvt) hw (by simp [Term.denote, h1]) hval
        · cases hv
      | _ => simp [SymInput.isOf] at hi
    · cases hp
  · cases x with
    | event i' value =>
      simp only [SymInput.isOf, beq_iff_eq] at hi
      subst hi
      obtain ⟨w, hw, rfl⟩ := map_some.1 hv
      have h0 := hvars 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at h0
      simp only [SymInput.validT] at hvt
      simp only [SymInput.tys, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hsrt
      exact names_holds hL hn hsrt _ (need_ok.1 hvt) hw (by simp [Term.denote, h0]) hval
    | _ => simp [SymInput.isOf] at hi
  · cases pure_ok.1 hvt; exact holds_tt

end

section
variable (L : Layout) (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (hc : v.caller.isData = true)

/-- The values of an unrolled step's constants in the model of a run whose step takes the input `x`: the selector holds
the input's kind, then each kind's values. -/
noncomputable def stepVals (n i b : Nat) (x : Input v) : List Val :=
  .int (x.pick : Int) :: (placeKinds (unrollKinds v (shapes v) n (i != 0)) (b + 1)).1.flatMap (kindVals L hc x)

/-- The step from `s` on `x` is one an unrolled step can take: the input's values fit the slots, the step stays within
the slots, the input is valid and the step does not fault. -/
def RunStep (s : State v) (x : Input v) : Prop :=
  (unrollVals L hc x).isSome ∧ StepFits L T P v s x ∧ x.Valid s ∧ ∀ f, (step T v s x).outcome ≠ .fault f

end

theorem length_flatMap_congr {α β γ : Type} {f : α → List β} {g : α → List γ} :
    (l : List α) → (∀ a ∈ l, (f a).length = (g a).length) → (l.flatMap f).length = (l.flatMap g).length
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons, List.length_append]
    rw [h a (by simp), length_flatMap_congr l fun b hb => h b (by simp [hb])]

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}
  (chk : Checked P E T v) (senv : StepEnv L (shapes v))

/-- One unrolled step from terms that denote the run's state `s`, whose constants hold the values of a step `x` can
take, holds its assertions and decodes to `x`. -/
theorem unrollOne_covers (hL : SortedLayout L) (S : SymState v) (i b : Nat) {s : State v}
    (hR : StateRel M L T (shapes v) S s) (hinv : Step.Inv P s) (h0 : i = 0 → s.pending = [])
    (hsrt : ∀ t ∈ (unrollOne L T P v senv S i b).1, (L.srt? t).isSome = true)
    (hnr : (unrollOne L T P v senv S i b).2.2.2.1 = []) {x : Input v} (hx : RunStep L T P v chk.callerData s x)
    (hvars : ∀ q (h : q < (stepVals L v chk.callerData senv.nT i b x).length),
      M.vars (b + q) = (stepVals L v chk.callerData senv.nT i b x)[q]) :
    (∀ a ∈ (unrollOne L T P v senv S i b).2.1, Holds M a) ∧
      (unrollOne L T P v senv S i b).2.2.1.decode M L chk.callerData = some x := by
  have hc := chk.callerData
  obtain ⟨hvs, hfit, hval, hno⟩ := hx
  obtain ⟨vs, hvs'⟩ := Option.isSome_iff_exists.1 hvs
  obtain ⟨hcf, hsf, -, -, -, hstf⟩ := hfit
  have hterms := unrollKinds_terms senv (ans := i != 0)
  have hsplit := placeKinds_split _ (b + 1) hterms
  have hat := placeKinds_at _ (b + 1) hterms
  have hmem := placeKinds_mem (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1)
  rcases hp : placeKinds (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1) with ⟨inps, e⟩
  rw [hp] at hsplit hat hmem
  dsimp only at hsplit hat hmem
  simp only [unrollOne, hp] at hsrt hnr ⊢
  simp only [stepVals, hp] at hvars
  have hb : M.vars b = .int (x.pick : Int) := by simpa using hvars 0 (by simp)
  have hlen : ∀ y ∈ inps, (kindVals L hc x y).length = y.tys.length := fun y hy => by
    obtain ⟨⟨p, hpk, c, rfl⟩, -⟩ := hat.2 y hy
    exact (forall2_length (kindVals_sorted hc hpk c x)).symm
  -- Each placed kind's constants hold its values, and its types have sorts.
  have hplaced : ∀ y ∈ inps, ∃ p ∈ unrollKinds v (shapes v) senv.nT (i != 0), ∃ c, y = p.2 c ∧
      (∀ q (h : q < (kindVals L hc x (p.2 c)).length), M.vars (c + q) = (kindVals L hc x (p.2 c))[q]) ∧
      ∀ t ∈ (p.2 c).tys, (L.srt? t).isSome = true := fun y hy => by
    obtain ⟨pre, post, c, hsp, hcb, p, hpk, rfl⟩ := hsplit y hy
    refine ⟨p, hpk, c, rfl, fun q hq => ?_, fun t ht => hsrt t (by
      simp only [List.singleton_append, List.mem_cons, List.mem_flatMap]; exact .inr ⟨_, hy, ht⟩)⟩
    have hpre : (pre.flatMap (kindVals L hc x)).length = (pre.flatMap SymInput.tys).length :=
      length_flatMap_congr pre fun z hz => hlen z (by rw [hsp]; simp [hz])
    have hidx : (inps.flatMap (kindVals L hc x))[(pre.flatMap (kindVals L hc x)).length + q]? =
        some (kindVals L hc x (p.2 c))[q] := by
      rw [hsp, List.flatMap_append, List.flatMap_cons, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_append_left hq]
      exact List.getElem?_eq_getElem hq
    have hl := (List.getElem?_eq_some_iff.1 hidx).1
    have h := hvars (1 + ((pre.flatMap (kindVals L hc x)).length + q)) (by rw [List.length_cons]; omega)
    rw [show b + (1 + ((pre.flatMap (kindVals L hc x)).length + q)) = c + q by omega] at h
    rw [h]
    have e1 : 1 + ((pre.flatMap (kindVals L hc x)).length + q) = ((pre.flatMap (kindVals L hc x)).length + q) + 1 := by
      omega
    simp only [e1, List.getElem_cons_succ]
    exact (List.getElem?_eq_some_iff.1 hidx).2
  generalize hoks : (inps.map fun inp => unrollKind L T P v senv S (.var b) inp).filterMap
    (fun | .ok x => some x | .error _ => none) = oks
  have hok : ∀ y ∈ oks, ∃ inp ∈ inps, unrollKind L T P v senv S (.var b) inp = .ok y := fun y hy => by
    rw [← hoks] at hy
    obtain ⟨r, hrm, hro⟩ := List.mem_filterMap.1 hy
    obtain ⟨inp, hi, rfl⟩ := List.mem_map.1 hrm
    refine ⟨inp, hi, ?_⟩
    cases hu : unrollKind L T P v senv S (.var b) inp with
    | error _ => simp [hu] at hro
    | ok x0 => simp [hu] at hro; rw [hro]
  have hall : ∀ inp ∈ inps, ∃ y, unrollKind L T P v senv S (.var b) inp = .ok y ∧ y ∈ oks := fun inp hi => by
    cases hu : unrollKind L T P v senv S (.var b) inp with
    | error r =>
      have := (List.filterMap_eq_nil_iff.1 hnr) _ (List.mem_map_of_mem (f := fun inp =>
        unrollKind L T P v senv S (.var b) inp) hi)
      simp [hu] at this
    | ok y => exact ⟨y, rfl, hoks ▸ List.mem_filterMap.2 ⟨_, List.mem_map_of_mem hi, by simp [hu]⟩⟩
  -- A kind the model picks is the input's, and decodes to it.
  have hpicked : ∀ inp ∈ inps, ∀ t, encodeStep L T P v senv S inp = .ok t →
      Holds M (selectsT (.var b) (inp, t)) → inp.decode M L hc = some x := by
    intro inp hi t ht hpk
    obtain ⟨p, hpk', c, rfl, hv, -⟩ := hplaced inp hi
    exact decode_of_isOf hc hpk' c hvs' hv (isOf_of_picks hc senv hpk' c hR hno hvs hv hb ht hpk)
  have hassert : ∀ y ∈ oks, Holds M y.2.2.1 := by
    intro y hy
    obtain ⟨inp, hi, hu⟩ := hok y hy
    obtain ⟨t, valid, wf, ht, hvt, hwf, rfl⟩ := unrollKind_ok senv hu
    simp only [holds_or, holds_not]
    by_cases hpk : Holds M (selectsT (.var b) (inp, t))
    · right
      obtain ⟨p, hpk', c, rfl, hv, hs⟩ := hplaced inp hi
      have hio := isOf_of_picks hc senv hpk' c hR hno hvs hv hb ht hpk
      have hdec := decode_of_isOf hc hpk' c hvs' hv hio
      have ex := step_encode chk senv hR hinv hdec ht
      have hcodes := ex.1.2 (codesFit_of_decode hdec hcf)
      have hsites := sites_of_decode senv ht hdec hsf
      have hcase := ((holds_andT _ _).1 hpk).2
      have hcond := ((ex.2 hcodes hsites hcase).1).2 hstf
      have hrel := ((ex.2 hcodes hsites hcase).2.1) hcond
      have hokH := (after_rel hR hdec hrel).1.2 hno
      have hvalid := valid_of_isOf hc hL hpk' c hvs' hv hio hs hval hR.fresh hvt
      simp only [holds_andT]
      exact ⟨SymInput.wf_of_decode hwf hdec, hcodes, hsites, hcond, hokH, hvalid⟩
    · exact .inl hpk
  -- The input's own kind is picked.
  have hpickEq : ∀ inp : SymInput v (shapes v) senv.nT, inp.pick = x.pick → Holds M (.eq (.var b) (.int inp.pick)) :=
    fun inp he => by
      simp only [Holds, Term.denote, hb, he, Val.toBool]
      show Val.beq (.int _) (.int _) = true
      simp [Val.beq]
  have hfound : ∃ inp ∈ inps, ∀ t, encodeStep L T P v senv S inp = .ok t →
      Holds M (selectsT (.var b) (inp, t)) := by
    have hone : ∀ inp : SymInput v (shapes v) senv.nT, inp.pick = x.pick → (∀ k j to w, inp ≠ .answer k j to w) →
        (∀ ty to w, inp ≠ .unmatched ty to w) → ∀ t, encodeStep L T P v senv S inp = .ok t →
        Holds M (selectsT (.var b) (inp, t)) := fun inp he ha hu t ht => by
      rw [selectsT, holds_andT, encodeStep_case_tt ht ha hu]
      exact ⟨hpickEq inp he, holds_tt⟩
    cases x with
    | command i' caller input =>
      obtain ⟨c, hc'⟩ := hmem (2, fun b => .command i' (.var b) (.var (b + 1))) (by simp [unrollKinds])
      exact ⟨_, hc', hone _ rfl (by simp) (by simp)⟩
    | query i' caller input =>
      obtain ⟨c, hc'⟩ := hmem (2, fun b => .query i' (.var b) (.var (b + 1))) (by simp [unrollKinds])
      exact ⟨_, hc', hone _ rfl (by simp) (by simp)⟩
    | event i' value =>
      obtain ⟨c, hc'⟩ := hmem (1, fun b => .event i' (.var b)) (by simp [unrollKinds])
      exact ⟨_, hc', hone _ rfl (by simp) (by simp)⟩
    | clock time =>
      obtain ⟨c, hc'⟩ := hmem (1, fun b => .clock (.var b)) (by simp [unrollKinds])
      exact ⟨_, hc', hone _ rfl (by simp) (by simp)⟩
    | answer to w =>
      obtain ⟨ty, value⟩ := w
      obtain ⟨p0, hf, hty⟩ := answer_found hno
      have hi0 : (i != 0) = true := by
        cases i with
        | zero => rw [h0 rfl] at hf; cases hf
        | succ => rfl
      obtain ⟨k, j, hout, hrej, hhit⟩ := answer_hit s to (toT := .int (Int.ofNat to)) hR.pending (by simp [Term.denote])
        senv hf
      have htk : answerTy (shapes v)[k].output (shapes v)[k].rejection = ty := by rw [hty, hout, hrej]
      have htd : ty.isData = true := by
        simp only [unrollVals, inputVals] at hvs
        split at hvs
        · assumption
        · cases hvs
      have hkm : k ∈ answerShapes (shapes v) := by
        simp only [answerShapes, List.mem_filter, List.mem_finRange, true_and]
        rw [htk]; exact htd
      obtain ⟨c, hc'⟩ := hmem (2, fun b => .answer k j (.var b) (.var (b + 1))) (by
        unfold unrollKinds
        rw [ite_eq_left hi0]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.2 ⟨k, hkm, List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩⟩))))
      refine ⟨_, hc', fun t ht => ?_⟩
      obtain ⟨p', hp', c', heq, hv, -⟩ := hplaced _ hc'
      have heq' : SymInput.answer k j (.var c) (.var (c + 1)) = p'.2 c' := heq
      have hcc : c = c' := by
        have hl := (hterms p' hp' c').1
        have ht' := (hterms p' hp' c').2
        rw [← heq'] at hl ht'
        simp only [SymInput.tys, List.length_cons, List.length_nil] at hl
        rw [← hl] at ht'
        simpa [SymInput.terms, List.range_succ] using ht'
      subst hcc
      have hk0 := kindVals_answer (k := k) (j := j) (toT := .var c) (valT := .var (c + 1)) hc hvs
      rw [heq'] at hk0
      have h0' := hv 0 (List.getElem?_eq_some_iff.1 hk0).1
      rw [(List.getElem?_eq_some_iff.1 hk0).2, Nat.add_zero] at h0'
      rw [selectsT, holds_andT, encodeStep_answer_case ht]
      refine ⟨hpickEq _ rfl, ?_⟩
      simpa [Holds, Term.denote, h0'] using hhit
  obtain ⟨inp0, hi0, hpk0⟩ := hfound
  obtain ⟨y0, hu0, hy0⟩ := hall inp0 hi0
  obtain ⟨t0, _, _, ht0, _, _, hy0e⟩ := unrollKind_ok senv hu0
  have hpick0 : Holds M y0.2.1 := by rw [hy0e]; exact hpk0 t0 ht0
  have hpick1 : Holds M (selectsT (.var b) y0.1) := by
    rw [hy0e]; exact hpk0 t0 ht0
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at ha
    rcases ha with ⟨y, hy, rfl⟩ | rfl
    · exact hassert y hy
    · exact (holds_anyT _).2 ⟨_, List.mem_map_of_mem hy0, hpick0⟩
  · simp only [UnrollStep.decode, UnrollStep.taken, UnrollStep.picks, Option.bind_eq_bind]
    obtain ⟨k', hk'⟩ : ∃ k', (oks.map (·.1)).find? (fun k =>
        ((selectsT (.var b) k).denote M).toBool) = some k' :=
      Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨_, List.mem_map_of_mem hy0, hpick1⟩)
    rw [hk']
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some hk')
    obtain ⟨inp, hi, hu⟩ := hok y hy
    obtain ⟨t, _, _, ht, _, _, hye⟩ := unrollKind_ok senv hu
    have hf := List.find?_some hk'
    rw [hye] at hf ⊢
    exact hpicked inp hi t ht hf

end

section
variable (L : Layout) (T : List TypeDecl) (P : List AnySite) (v : ServiceV) (hc : v.caller.isData = true)

/-- Every step of the run is one an unrolled step can take (`RunStep`). -/
abbrev RunFits : State v → List (Input v) → Prop := Step.EachStep T (RunStep L T P v hc)

/-- Every step of the run is within the slots: its input's values fit them and the step stays within them. The part of
`RunStep` that is the bounds; the rest is what `Step.Assumption.ofRuns` names. -/
abbrev RunIn : State v → List (Input v) → Prop :=
  Step.EachStep T fun s x => (unrollVals L hc x).isSome ∧ StepFits L T P v s x

/-- A run within the slots on which `Step.Assumption.ofRuns` holds is one an unrolled run can take. -/
theorem runFits_of : (s : State v) → (xs : List (Input v)) → RunIn L T P v hc s xs →
    (∀ a ∈ Step.Assumption.ofRuns, a.Holds T s xs) → RunFits L T P v hc s xs
  | _, [], _, _ => trivial
  | s, x :: xs, ⟨hin, hins⟩, hA => by
    have hv : Step.ValidRun T s (x :: xs) := hA .validInputs (by simp [Step.Assumption.ofRuns])
    have hn : Step.NoFaultRun T s (x :: xs) := hA .noFault (by simp [Step.Assumption.ofRuns])
    refine ⟨⟨hin.1, hin.2, hv.1, hn.1⟩, runFits_of _ xs hins fun a ha => ?_⟩
    simp only [Step.Assumption.ofRuns, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact hv.2
    · exact hn.2

/-- The values of an unrolled run's constants, from step `i` with its selector at the constant `b`, in the model of the
run on the inputs `xs`. -/
noncomputable def runVals (n : Nat) : Nat → Nat → List (Input v) → List Val
  | _, _, [] => []
  | i, b, x :: xs => stepVals L v hc n i b x ++
    runVals n (i + 1) (placeKinds (unrollKinds v (shapes v) n (i != 0)) (b + 1)).2 xs

end

theorem forall2_flatMap {α β γ : Type} {R : β → γ → Prop} {f : α → List β} {g : α → List γ} :
    (l : List α) → (∀ a ∈ l, Forall2 R (f a) (g a)) → Forall2 R (l.flatMap f) (l.flatMap g)
  | [], _ => trivial
  | a :: l, h => by
    simp only [List.flatMap_cons]
    exact forall2_append (h a (by simp)) (forall2_flatMap l fun b hb => h b (by simp [hb]))

theorem forall2_sorted_of {L : Layout} : {tys : List Ty} → {ws : List Val} → Forall2 (SortedIf L) tys ws →
    (∀ t ∈ tys, ∃ w, Sorted L t w) → Forall2 (Sorted L) tys ws
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩, he => ⟨h1 (he _ (by simp)), forall2_sorted_of h2 fun t ht => he t (by simp [ht])⟩

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}
  (chk : Checked P E T v) (senv : StepEnv L (shapes v))

/-- An unrolled step's constants and their values in a run's model: one value per constant, of its sort wherever the
sort holds one, all data. -/
theorem unrollOne_vals (S : SymState v) (i b : Nat) (x : Input v) :
    Forall2 (SortedIf L) (unrollOne L T P v senv S i b).1 (stepVals L v chk.callerData senv.nT i b x) ∧
      ∀ t ∈ (unrollOne L T P v senv S i b).1, t.isData = true := by
  have hat := placeKinds_at _ (b + 1) (unrollKinds_terms senv (ans := i != 0))
  rcases hp : placeKinds (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1) with ⟨inps, e⟩
  rw [hp] at hat
  dsimp only at hat
  simp only [unrollOne, stepVals, hp]
  refine ⟨⟨fun _ => ⟨_, rfl⟩, forall2_flatMap inps fun y hy => ?_⟩, fun t ht => ?_⟩
  · obtain ⟨⟨p, hpk, c, rfl⟩, -⟩ := hat.2 y hy
    exact kindVals_sorted chk.callerData hpk c x
  · simp only [List.singleton_append, List.mem_cons, List.mem_flatMap] at ht
    rcases ht with rfl | ⟨y, hy, ht⟩
    · rfl
    · obtain ⟨⟨p, hpk, c, rfl⟩, -⟩ := hat.2 y hy
      exact (unrollKinds_shape chk.callerData hpk c).2.2 t ht

/-- The constant after an unrolled step is past its values. -/
theorem unrollOne_next_vals (S : SymState v) (i b : Nat) (x : Input v) :
    (unrollOne L T P v senv S i b).2.2.2.2 = b + (stepVals L v chk.callerData senv.nT i b x).length := by
  rw [unrollOne_next senv S i b, forall2_length (unrollOne_vals chk senv S i b x).1]

theorem unrollSteps_vals : (xs : List (Input v)) → (S : SymState v) → (i b : Nat) →
    Forall2 (SortedIf L) (unrollSteps L T P v senv S i b xs.length).1 (runVals L v chk.callerData senv.nT i b xs) ∧
      ∀ t ∈ (unrollSteps L T P v senv S i b xs.length).1, t.isData = true
  | [], _, _, _ => by simp [unrollSteps, runVals, Forall2]
  | x :: xs, S, i, b => by
    have h1 := unrollOne_vals chk senv S i b x
    rcases ho : unrollOne L T P v senv S i b with ⟨tys, asserts, st, refused, b'⟩
    have hb' : b' = (placeKinds (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1)).2 := by
      have : (unrollOne L T P v senv S i b).2.2.2.2 = b' := by rw [ho]
      rw [← this]; rfl
    have ih := unrollSteps_vals xs st.after (i + 1) b'
    rw [ho] at h1
    simp only [List.length_cons, unrollSteps, ho, runVals, ← hb'] at ih ⊢
    exact ⟨forall2_append h1.1 ih.1, fun t ht => (List.mem_append.1 ht).elim (h1.2 t) (ih.2 t)⟩

/-- The steps of an unrolled run from terms that denote the run's state `s`, whose constants hold a fitting run's
values, hold their assertions and are that run. -/
theorem unrollSteps_covers (hL : SortedLayout L) : (xs : List (Input v)) → (S : SymState v) → (i b : Nat) →
    {s : State v} → StateRel M L T (shapes v) S s → Step.Inv P s → (i = 0 → s.pending = []) →
    (∀ t ∈ (unrollSteps L T P v senv S i b xs.length).1, (L.srt? t).isSome = true) →
    (unrollSteps L T P v senv S i b xs.length).2.2.2 = [] → RunFits L T P v chk.callerData s xs →
    (∀ q (h : q < (runVals L v chk.callerData senv.nT i b xs).length),
      M.vars (b + q) = (runVals L v chk.callerData senv.nT i b xs)[q]) →
    (∀ a ∈ (unrollSteps L T P v senv S i b xs.length).2.1, Holds M a) ∧
      UnrollRun L T M chk.callerData s (unrollSteps L T P v senv S i b xs.length).2.2.1 xs
  | [], _, _, _, _, _, _, _, _, _, _, _ => by simp [unrollSteps, UnrollRun]
  | x :: xs, S, i, b, s, hR, hinv, h0, hsrt, hnr, hfits, hvars => by
    have hnext := unrollOne_next_vals chk senv S i b x
    have hlen := forall2_length (unrollOne_vals chk senv S i b x).1
    rcases ho : unrollOne L T P v senv S i b with ⟨tys, asserts, st, refused, b'⟩
    have hb' : b' = (placeKinds (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1)).2 := by
      have : (unrollOne L T P v senv S i b).2.2.2.2 = b' := by rw [ho]
      rw [← this]; rfl
    rw [ho] at hnext hlen
    dsimp only at hnext hlen
    simp only [List.length_cons, unrollSteps, ho, runVals, ← hb'] at hsrt hnr hvars ⊢
    obtain ⟨hfit, hfits⟩ := hfits
    have hvars1 : ∀ q (h : q < (stepVals L v chk.callerData senv.nT i b x).length),
        M.vars (b + q) = (stepVals L v chk.callerData senv.nT i b x)[q] := fun q h => by
      rw [hvars q (by simp; omega)]
      exact List.getElem_append_left h
    have hc1 := unrollOne_covers chk senv hL S i b hR hinv h0
      (by rw [ho]; exact fun t ht => hsrt t (List.mem_append_left _ ht))
      (by rw [ho]; exact (List.append_eq_nil_iff.1 hnr).1) hfit hvars1
    rw [ho] at hc1
    dsimp only at hc1
    have hat := unrollOne_at chk senv S i b hR hinv (by rw [ho]; exact hc1.1) (by rw [ho]; exact hc1.2)
    rw [ho] at hat
    have ih := unrollSteps_covers hL xs st.after (i + 1) b' hat.2.2.1 (step_inv T chk.reach s hinv x) (fun h => by omega)
      (fun t ht => hsrt t (List.mem_append_right _ ht)) (List.append_eq_nil_iff.1 hnr).2 hfits fun q h => by
        have e : b' + q = b + ((stepVals L v chk.callerData senv.nT i b x).length + q) := by omega
        rw [e, hvars _ (by simp; omega), List.getElem_append_right (by omega)]
        simp
    exact ⟨fun a ha => (List.mem_append.1 ha).elim (hc1.1 a) (ih.1 a), hc1.2, hat, ih.2⟩

end

section
variable {L : Layout} {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}
  (chk : Checked P E T v) (senv : StepEnv L (shapes v))

/-- Every run is a model of its unrolled script: where no input kind's encoding was refused, a run of `d` inputs from
the initial state whose inputs fit the slots and are valid, whose steps stay within the slots and do not fault, gives a
model whose variables hold values of their sorts, whose steps are that run, and which satisfies every assertion of the
run. So the run with a goal has no model exactly when no such run satisfies the goal (`UnrollBase.holds_withGoal`):
generate's "unreached within `d` steps" rests on this. -/
theorem runs_covered (hL : SortedLayout L) {d : Nat} {B : UnrollBase v senv.nT}
    (hB : unrollBase L T P v senv d = .ok B) (hnr : B.refused = [])
    {xs : List (Input v)} (hlen : xs.length = d) (hfits : RunFits L T P v chk.callerData (Step.State.init v) xs) :
    ∃ M : Model, (∀ n (h : n < B.tys.length), VarSorted L B.tys[n] (M.vars n)) ∧
      UnrollRun L T M chk.callerData (Step.State.init v) B.steps xs ∧ ∀ a ∈ B.asserts, Holds M a := by
  subst hlen
  simp only [unrollBase] at hB
  obtain ⟨S0, hS0, hB⟩ := bind_ok.1 hB
  obtain ⟨dts, hdts, hB⟩ := bind_ok.1 hB
  have hv := unrollSteps_vals chk senv xs S0 0 0
  have hcov := unrollSteps_covers (M := coverModel (runVals L v chk.callerData senv.nT 0 0 xs)) chk senv hL xs S0 0 0
    (init_rel (need_ok.1 hS0)) Step.init_inv (fun _ => rfl)
  rcases hr : unrollSteps L T P v senv S0 0 0 xs.length with ⟨tys, asserts, steps, refused⟩
  rw [hr] at hB hv hcov
  obtain ⟨vars, hvars, hB⟩ := bind_ok.1 hB
  cases pure_ok.1 hB
  have hsrt : ∀ t ∈ tys, (L.srt? t).isSome = true := mapM_some_mem (by rw [mapM_need hvars]; rfl)
  have hsorted := forall2_sorted_of hv.1 fun t ht => sorted_exists (need_ok.1 hdts) t (hsrt t ht) (hv.2 t ht)
  have hc := hcov hsrt hnr hfits fun q h => by
    rw [Nat.zero_add]
    exact coverModel_vars (List.getElem?_eq_getElem h)
  exact ⟨_, fun n h => varSorted_of_sorted (forall2_sorted_vars hsorted n h), hc.2, hc.1⟩

end

end Tazuna.Smt
