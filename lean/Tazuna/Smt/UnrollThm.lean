import Tazuna.Smt.DecodeTotal
import Tazuna.Smt.Cover

/-! What an unrolled run means. Where a step's terms say what its result is (`StepOut.Rel`, T2), the state its
`StepOut.after` reads off the terms denotes the result's state exactly when the step does not fault (`after_rel`). The
denotation is `StateRel`, with the pending requests as a multiset, so the next step's theorems start from the run's own
state: no decoding between steps and no step congruence is needed. The initial state's constants denote the initial
state (`init_rel`), so by induction every model of an unrolled run is a run of the inputs it decodes to
(`unroll_decode`). -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV}

theorem denote_ite_pos {c : Term} (h : Holds M c) (a b : Term) : (Term.ite c a b).denote M = a.denote M := by
  simp only [Term.denote, show (c.denote M).toBool = true from h, ite_true]

theorem denote_ite_neg {c : Term} (h : ¬ Holds M c) (a b : Term) : (Term.ite c a b).denote M = b.denote M := by
  simp only [Term.denote, show (c.denote M).toBool = false by simpa [Holds] using h]; rfl

theorem machinesRel_ite_pos {c : Term} (h : Holds M c) : (ms : List (MachineV v.records v.event)) →
    (a b : PerMachine (fun _ => Term) ms) → (sms : Step.Machines ms) → MachinesRel M L T ms a sms →
    MachinesRel M L T ms (PerMachine.zipWith (Term.ite c) a b) sms
  | [], .nil, .nil, .nil, _ => trivial
  | _ :: ms, .cons _ xs, .cons _ ys, .cons _ sms, h' => by
    obtain ⟨h1, h2⟩ := h'
    exact ⟨by simpa only [denote_ite_pos h] using h1, machinesRel_ite_pos h ms xs ys sms h2⟩

theorem machinesRel_ite_neg {c : Term} (h : ¬ Holds M c) : (ms : List (MachineV v.records v.event)) →
    (a b : PerMachine (fun _ => Term) ms) → (sms : Step.Machines ms) → MachinesRel M L T ms b sms →
    MachinesRel M L T ms (PerMachine.zipWith (Term.ite c) a b) sms
  | [], .nil, .nil, .nil, _ => trivial
  | _ :: ms, .cons _ xs, .cons _ ys, .cons _ sms, h' => by
    obtain ⟨h1, h2⟩ := h'
    exact ⟨by simpa only [denote_ite_neg h] using h1, machinesRel_ite_neg h ms xs ys sms h2⟩

variable {shs : List (PendingShape v.event)}

/-- Where `c` holds, the state whose components are `a`'s where `c` holds denotes what `a` denotes. -/
theorem stateRel_ite_pos {c : Term} (h : Holds M c) {a : SymState v} (b : SymState v) {s : State v}
    (hR : StateRel M L T shs a s) : StateRel M L T shs (SymState.ite c a b) s where
  records := by simpa only [SymState.ite, denote_ite_pos h] using hR.records
  now := by simpa only [SymState.ite, denote_ite_pos h] using hR.now
  fresh := by simpa only [SymState.ite, denote_ite_pos h] using hR.fresh
  nextId := by simpa only [SymState.ite, denote_ite_pos h] using hR.nextId
  pending := by simpa only [SymState.ite, denote_ite_pos h] using hR.pending
  machines := machinesRel_ite_pos h _ _ _ _ hR.machines

theorem stateRel_ite_neg {c : Term} (h : ¬ Holds M c) (a : SymState v) {b : SymState v} {s : State v}
    (hR : StateRel M L T shs b s) : StateRel M L T shs (SymState.ite c a b) s where
  records := by simpa only [SymState.ite, denote_ite_neg h] using hR.records
  now := by simpa only [SymState.ite, denote_ite_neg h] using hR.now
  fresh := by simpa only [SymState.ite, denote_ite_neg h] using hR.fresh
  nextId := by simpa only [SymState.ite, denote_ite_neg h] using hR.nextId
  pending := by simpa only [SymState.ite, denote_ite_neg h] using hR.pending
  machines := machinesRel_ite_neg h _ _ _ _ hR.machines

/-- A step that takes a counter and leaves the rest. -/
theorem stateRel_bump {S : SymState v} {s : State v} (hR : StateRel M L T shs S s) :
    StateRel M L T shs { S with fresh := .add S.fresh (.int 1) } { s with fresh := s.fresh + 1 } where
  records := hR.records
  now := hR.now
  fresh := by simp only [Term.denote, hR.fresh, Val.toInt]; rfl
  nextId := hR.nextId
  pending := hR.pending
  machines := hR.machines

/-- A step's end that does not fault: its `ok` term holds exactly when the result does not fault, and then the state
its terms end with denotes the result's state. -/
theorem finished_after {fo : FinishOut v} {s0 : State v} {a : Step.Acc v} {outcome : Outcome} {r : Result v}
    (hf : Finished M L T shs fo s0 a outcome r) (hacc : ∀ f, outcome ≠ .fault f) {now : Term}
    (hnow : now.denote M = .int a.state.now) :
    (Holds M fo.ok ↔ ∀ f, r.outcome ≠ .fault f) ∧ (Holds M fo.ok → StateRel M L T shs (fo.state now) r.state) := by
  obtain ⟨hF, hm⟩ := hf
  have hok : Holds M fo.ok ↔ ¬ Holds M fo.settle.faultT ∧ brokenIn M fo.invariants = [] ∧
      checksBroken L T M v.machines fo.checks = [] := by
    simp only [FinishOut.ok, holds_andT, holds_not, holds_allT_rules]
    exact and_congr_right fun _ => and_congr_right fun _ => ⟨nil_of_instHold _ _, instHold_of_nil _ _⟩
  cases hfo : fo.settle.fault? M with
  | some f =>
    rw [hfo] at hm hF
    subst hm
    have hn : ¬ Holds M fo.ok := fun h => (hok.1 h).1 (by simp [Holds, hF, Val.toBool])
    exact ⟨⟨fun h => absurd h hn, fun h => absurd rfl (h f)⟩, fun h => absurd h hn⟩
  | none =>
    rw [hfo] at hm hF
    have hF' : ¬ Holds M fo.settle.faultT := by simp [Holds, hF, Val.toBool]
    simp only at hm
    split at hm
    · rename_i n rest hl
      subst hm
      have hn : ¬ Holds M fo.ok := fun h => by
        obtain ⟨-, h1, h2⟩ := hok.1 h
        rw [h1, h2] at hl
        cases hl
      exact ⟨⟨fun h => absurd h hn, fun h => absurd rfl (h _)⟩, fun h => absurd h hn⟩
    · rename_i hl
      obtain ⟨recs, ms, fr, evs, ps, rfl, hrec, hms, hfr, hni, hpend⟩ := hm
      have hok' : Holds M fo.ok := hok.2 ⟨hF', List.append_eq_nil_iff.1 hl⟩
      refine ⟨⟨fun _ f h => hacc f h, fun _ => hok'⟩, fun _ => ⟨hrec, hnow, ?_, hni, hpend, hms⟩⟩
      simpa [FinishOut.state] using hfr

/-- What an unrolled step's terms leave: where a step's terms say what its result from `s` is, the step's `ok` term
holds exactly when the step does not fault, and then the state `StepOut.after` reads off the terms denotes the
result's state. -/
theorem after_rel {n : Nat} {hc : v.caller.isData = true} {S : SymState v} {s : State v}
    (hR : StateRel M L T (shapes v) S s) {out : StepOut v} {inp : SymInput v (shapes v) n} {x : Input v}
    (hx : inp.decode M L hc = some x) (hrel : out.Rel M L T (shapes v) s x (step T v s x)) :
    (Holds M (out.after S inp).1 ↔ ∀ f, (step T v s x).outcome ≠ .fault f) ∧
    (Holds M (out.after S inp).1 → StateRel M L T (shapes v) (out.after S inp).2 (step T v s x).state) := by
  have hunm : ∀ u, StepOut.Rel M L T (shapes v) s (.unmatched u) x (step T v s x) →
      (Holds M (StepOut.after S (.unmatched u) inp).1 ↔ ∀ f, (step T v s x).outcome ≠ .fault f) ∧
      (Holds M (StepOut.after S (.unmatched u) inp).1 → StateRel M L T (shapes v) (StepOut.after S (.unmatched u) inp).2
        (step T v s x).state) := fun u h => by
    generalize step T v s x = r at h ⊢
    have hf : Holds M (Term.bool false) → False := fun h => by simp [Holds, Term.denote, Val.toBool] at h
    cases x with
    | answer =>
      simp only [StepOut.Rel] at h
      subst h
      exact ⟨⟨fun h' => (hf h').elim, fun h' => absurd rfl (h' .answerUnmatched)⟩, fun h' => (hf h').elim⟩
    | _ => simp only [StepOut.Rel] at h
  cases inp with
  | command i sc si =>
    obtain ⟨caller, input, rfl, -, -⟩ := decode_command hx
    cases out with
    | command o =>
      generalize step T v s _ = r at hrel ⊢
      simp only [StepOut.Rel] at hrel
      simp only [StepOut.after, holds_andT, holds_or, holds_not, holds_allT_rules]
      have hbump := stateRel_bump hR
      -- Where the step is not admitted, it takes a counter and leaves the rest.
      have notAdm : ¬ (Holds M o.callerOk ∧ brokenIn M o.rules = [] ∧ Holds M o.decided.ok) →
          r.state = { s with fresh := s.fresh + 1 } → (∀ f, r.outcome ≠ .fault f) →
          (((¬ (Holds M o.callerOk ∧ brokenIn M o.rules = [] ∧ Holds M o.decided.ok) ∨
              brokenIn M o.decided.ensures = []) ∧
            (¬ ((Holds M o.callerOk ∧ brokenIn M o.rules = [] ∧ Holds M o.decided.ok) ∧
              brokenIn M o.decided.ensures = []) ∨ Holds M o.finish.ok)) ↔ ∀ f, r.outcome ≠ .fault f) ∧
          (((¬ (Holds M o.callerOk ∧ brokenIn M o.rules = [] ∧ Holds M o.decided.ok) ∨
              brokenIn M o.decided.ensures = []) ∧
            (¬ ((Holds M o.callerOk ∧ brokenIn M o.rules = [] ∧ Holds M o.decided.ok) ∧
              brokenIn M o.decided.ensures = []) ∨ Holds M o.finish.ok)) → StateRel M L T (shapes v) (SymState.ite (andT (andT o.callerOk (andT (allT (o.rules.map (·.2)))
            o.decided.ok)) (allT (o.decided.ensures.map (·.2)))) (o.finish.state S.now)
              { S with fresh := .add S.fresh (.int 1) }) r.state) := fun hadm hst hno =>
        ⟨⟨fun _ => hno, fun _ => ⟨.inl hadm, .inl fun h => hadm h.1⟩⟩, fun _ => hst ▸ stateRel_ite_neg
          (by simp only [holds_andT, holds_allT_rules]; exact fun h => hadm h.1) _ hbump⟩
      split at hrel
      · rename_i hcall
        have hcall' : Holds M o.callerOk := hcall
        split at hrel
        · rename_i m ms hr
          subst hrel
          exact notAdm (fun h => by rw [hr] at h; cases h.2.1) rfl (fun f h => by cases h)
        · rename_i hr
          split at hrel
          · rename_i hok
            have hok' : Holds M o.decided.ok := hok
            have hadm : Holds M o.callerOk ∧ brokenIn M o.rules = [] ∧ Holds M o.decided.ok := ⟨hcall', hr, hok'⟩
            split at hrel
            · rename_i m ms he
              subst hrel
              have hne : ¬ brokenIn M o.decided.ensures = [] := by simp [he]
              exact ⟨⟨fun h => (hne (h.1.resolve_left fun h' => h' hadm)).elim, fun h => absurd rfl (h _)⟩,
                fun h => (hne (h.1.resolve_left fun h' => h' hadm)).elim⟩
            · rename_i he
              have hreach : Holds M (andT (andT o.callerOk (andT (allT (o.rules.map (·.2))) o.decided.ok))
                  (allT (o.decided.ensures.map (·.2)))) := by
                simp only [holds_andT, holds_allT_rules]; exact ⟨hadm, he⟩
              have fin := finished_after hrel (fun f h => by cases h) (now := S.now) hR.now
              exact ⟨⟨fun h => fin.1.1 (h.2.resolve_left fun h' => h' ⟨hadm, he⟩),
                fun h => ⟨.inr he, .inr (fin.1.2 h)⟩⟩,
                fun h => stateRel_ite_pos hreach _ (fin.2 (h.2.resolve_left fun h' => h' ⟨hadm, he⟩))⟩
          · rename_i hok
            obtain ⟨hst, j, hj, -⟩ := hrel
            exact notAdm (fun h => hok h.2.2) hst (fun f h => by rw [hj] at h; cases h)
      · rename_i hcall
        subst hrel
        exact notAdm (fun h => hcall h.1) rfl (fun f h => by cases h)
    | unmatched u => exact hunm u hrel
    | _ => simp only [StepOut.Rel] at hrel
  | query i sc si =>
    obtain ⟨caller, input, rfl, -, -⟩ := decode_query hx
    cases out with
    | query o =>
      refine ⟨⟨fun _ => query_no_fault T s i caller input, fun _ => holds_tt⟩, fun _ => ?_⟩
      simp only [StepOut.after]
      rw [hrel.1]
      exact hR
    | unmatched u => exact hunm u hrel
    | _ => simp only [StepOut.Rel] at hrel
  | answer k j to value | unmatched t to value =>
    obtain ⟨-, to, value, rfl, -, -⟩ := decode_answer hx
    cases out with
    | answer o =>
      generalize step T v s _ = r at hrel ⊢
      simp only [StepOut.Rel] at hrel
      simp only [StepOut.after, holds_or, holds_not, holds_allT_rules]
      split at hrel
      · rename_i m ms hr
        subst hrel
        have hn : ¬ brokenIn M o.rules = [] := by simp [hr]
        exact ⟨⟨(fun _ f h => by cases h), fun _ => .inl hn⟩,
          fun _ => stateRel_ite_neg (fun h => hn ((holds_allT_rules _).1 h)) _ hR⟩
      · rename_i hr
        have fin := finished_after hrel (fun f h => nomatch h) (now := S.now) hR.now
        refine ⟨⟨fun h => fin.1.1 (h.resolve_left (fun h' => h' hr)), fun h => .inr (fin.1.2 h)⟩,
          fun h => stateRel_ite_pos ((holds_allT_rules _).2 hr) _ (fin.2 (h.resolve_left (fun h' => h' hr)))⟩
    | unmatched u => exact hunm u hrel
    | _ => simp only [StepOut.Rel] at hrel
  | event i sv =>
    obtain ⟨value, rfl, -⟩ := decode_event hx
    cases out with
    | event o => exact finished_after hrel (fun f h => nomatch h) hR.now
    | unmatched u => exact hunm u hrel
    | _ => simp only [StepOut.Rel] at hrel
  | clock st =>
    obtain ⟨time, rfl, hst⟩ := decode_clock hx
    cases out with
    | clock o =>
      generalize step T v s _ = r at hrel ⊢
      simp only [StepOut.Rel] at hrel
      simp only [StepOut.after, holds_or, holds_not, holds_andT]
      split at hrel
      · rename_i hfw
        have hfw' : Holds M o.forward := hfw
        split at hrel
        · rename_i hover
          subst hrel
          have hov : Holds M o.over := hover
          exact ⟨⟨fun h => ((h.resolve_left (fun h' => h' hfw')).1 hov).elim, fun h => absurd rfl (h _)⟩,
            fun h => ((h.resolve_left (fun h' => h' hfw')).1 hov).elim⟩
        · rename_i hover
          have hov : ¬ Holds M o.over := by simpa [Holds] using hover
          have fin := finished_after hrel (fun f h => nomatch h) (now := st) hst
          exact ⟨⟨fun h => fin.1.1 (h.resolve_left (fun h' => h' hfw')).2, fun h => .inr ⟨hov, fin.1.2 h⟩⟩,
            fun h => stateRel_ite_pos hfw' _ (fin.2 (h.resolve_left (fun h' => h' hfw')).2)⟩
      · rename_i hfw
        subst hrel
        exact ⟨⟨(fun _ f h => by cases h), fun _ => .inl hfw⟩, fun _ => stateRel_ite_neg hfw _ hR⟩
    | unmatched u => exact hunm u hrel
    | _ => simp only [StepOut.Rel] at hrel

end

section
variable {M : Model} {L : Layout}

/-- A collection's constant: the slots hold the items in order, then the default items in free slots. -/
theorem collT_some {c : Ty} {item : List Ty} {xs : List (SlotItems item.length)} {a : Term}
    (h : collT L c item xs = some a) :
    ∃ d n dt m sv, L.find? c = some (d, n) ∧ L.find? (.tuple (Ty.bool :: item)) = some (dt, m) ∧ sv.length = n ∧
      a.denote M = slotsVal d dt sv ∧ (∀ p ∈ sv, p.2.length = item.length) ∧
      occupied sv = xs.map fun x => Term.denotes M x.1 := by
  unfold collT at h
  cases h1 : L.find? c with
  | none => simp [h1] at h
  | some p =>
    obtain ⟨d, n⟩ := p
    cases h2 : L.find? (.tuple (Ty.bool :: item)) with
    | none => simp [h1, h2] at h
    | some q =>
      obtain ⟨dt, m⟩ := q
      cases h3 : defaultItems L item with
      | error e => simp [h1, h2, h3, Except.toOption] at h
      | ok dflt =>
        simp only [h1, h2, h3, Except.toOption, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · rename_i hle
          cases h
          refine ⟨d, n, dt, m, (xs.map fun x => (true, Term.denotes M x.1)) ++
            List.replicate (n - xs.length) (false, Term.denotes M dflt.1), rfl, rfl, by simp; omega, ?_, ?_, ?_⟩
          · simp only [slotsTerm, Term.denote_share, Term.denote, slotsVal, denotes_eq_map, List.map_append,
              List.map_map, List.map_replicate]
            congr 2
            · exact List.map_congr_left fun x _ => by simp [Term.denote, denotes_eq_map, tt]
          · intro p hp
            simp only [List.mem_append, List.mem_map, List.mem_replicate] at hp
            rcases hp with ⟨x, -, rfl⟩ | ⟨-, rfl⟩
            · simp [denotes_eq_map, x.2]
            · simp [denotes_eq_map, dflt.2]
          · simp [occupied, List.filterMap_append, List.filterMap_map, Function.comp_def]
        · cases h

theorem forall2_items1 {t : Ty} : {xs : List t.den} → {items : List (SlotItems 1)} →
    xs.mapM (fun x => (dataT L t x).map fun a => (⟨[a], rfl⟩ : SlotItems 1)) = some items →
    (∀ x ∈ xs, ∀ a, dataT L t x = some a → RelV L t x (a.denote M)) →
    Forall2 (fun y vs => ∃ z, vs = [z] ∧ RelV L t y z) xs (items.map fun i => Term.denotes M i.1)
  | [], _, h, _ => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; trivial
  | x :: xs, _, h, ih => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Option.map_eq_some_iff] at h
    obtain ⟨_, ⟨a, ha, rfl⟩, rest, hrest, rfl⟩ := h
    exact ⟨⟨a.denote M, rfl, ih x (by simp) a ha⟩, forall2_items1 hrest fun y hy => ih y (by simp [hy])⟩

theorem forall2_items2 {k w : Ty} : {xs : List (k.den × w.den)} → {items : List (SlotItems 2)} →
    xs.mapM (fun e => (dataT L k e.1).bind fun a => (dataT L w e.2).map fun b => (⟨[a, b], rfl⟩ : SlotItems 2)) =
      some items →
    (∀ e ∈ xs, ∀ a, dataT L k e.1 = some a → RelV L k e.1 (a.denote M)) →
    (∀ e ∈ xs, ∀ b, dataT L w e.2 = some b → RelV L w e.2 (b.denote M)) →
    Forall2 (fun e vs => ∃ zk zv, vs = [zk, zv] ∧ RelV L k e.1 zk ∧ RelV L w e.2 zv) xs
      (items.map fun i => Term.denotes M i.1)
  | [], _, h, _, _ => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; trivial
  | e :: xs, _, h, ik, iw => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Option.map_eq_some_iff] at h
    obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, rest, hrest, rfl⟩ := h
    exact ⟨⟨a.denote M, b.denote M, rfl, ik e (by simp) a ha, iw e (by simp) b hb⟩,
      forall2_items2 hrest (fun y hy => ik y (by simp [hy])) (fun y hy => iw y (by simp [hy]))⟩

mutual
/-- A value's constant denotes it. -/
theorem dataT_rel : (t : Ty) → (x : t.den) → (a : Term) → dataT L t x = some a → RelV L t x (a.denote M)
  | .int, x, a, h | .date, x, a, h => by cases h; rfl
  | .str, x, a, h => by cases h; rfl
  | .dsl .fresh _, x, a, h => by cases h; rfl
  | .id, x, a, h => by
    obtain ⟨⟨d, n⟩, hf, rfl⟩ := map_some.1 h
    exact ⟨d, n, hf, Val.denote_term M _⟩
  | .adt 0 _ [[], []], x, a, h => by cases h; exact ⟨rfl, rfl⟩
  | .adt (i + 1) b vs, x, a, h => by
    simp only [dataT] at h
    split at h
    · rename_i d n hf
      exact ⟨d, n, hf, dataAlts_rel d 0 vs x a h⟩
    · cases h
  | .tuple ts, x, a, h => by
    simp only [dataT] at h
    split at h
    · rename_i d n hf
      obtain ⟨as, has, rfl⟩ := map_some.1 h
      exact ⟨d, n, _, hf, rfl, dataTs_rel ts x as has⟩
    · cases h
  | .bag t, xs, a, h => by
    simp only [dataT] at h
    obtain ⟨items, hitems, hc⟩ := bind_some.1 h
    obtain ⟨d, n, dt, m, sv, hf, hft, hl, hv, hw, hocc⟩ := collT_some (M := M) hc
    refine ⟨d, n, dt, m, sv, hf, hft, hl, hv, hw, xs, .refl _, ?_⟩
    unfold Holds2
    rw [hocc]
    exact forall2_items1 hitems fun y _ a ha => dataT_rel t y a ha
  | .list t, xs, a, h => by
    simp only [dataT] at h
    obtain ⟨items, hitems, hc⟩ := bind_some.1 h
    obtain ⟨d, n, dt, m, sv, hf, hft, hl, hv, hw, hocc⟩ := collT_some (M := M) hc
    refine ⟨d, n, dt, m, sv, hf, hft, hl, hv, hw, ?_⟩
    unfold Holds2
    rw [hocc]
    exact forall2_items1 hitems fun y _ a ha => dataT_rel t y a ha
  | .table k w, x, a, h => by
    simp only [dataT] at h
    obtain ⟨items, hitems, hc⟩ := bind_some.1 h
    obtain ⟨d, n, dt, m, sv, hf, hft, hl, hv, hw, hocc⟩ := collT_some (M := M) hc
    refine ⟨d, n, dt, m, sv, hf, hft, hl, hv, hw, x.1, .refl _, ?_⟩
    unfold Holds2
    rw [hocc]
    exact forall2_items2 hitems (fun e _ a ha => dataT_rel k e.1 a ha) (fun e _ b hb => dataT_rel w e.2 b hb)
theorem dataTs_rel : (ts : List Ty) → (x : Ty.dens ts) → (as : List Term) → dataTs L ts x = some as →
    RelVs L ts x (Term.denotes M as)
  | [], _, _, h => by cases h; rfl
  | t :: ts, (x, xs), _, h => by
    obtain ⟨a, ha, h⟩ := bind_some.1 h
    obtain ⟨as, has, rfl⟩ := map_some.1 h
    exact ⟨a.denote M, Term.denotes M as, rfl, dataT_rel t x a ha, dataTs_rel ts xs as has⟩
theorem dataAlts_rel (d : Nat) : (k : Nat) → (vs : List (List Ty)) → (x : Ty.alts vs) → (a : Term) →
    dataAlts L d k vs x = some a → RelAlts L d k vs x (a.denote M)
  | k, fs :: _, .inl x, _, h => by
    obtain ⟨as, has, rfl⟩ := map_some.1 h
    exact ⟨_, rfl, dataTs_rel fs x as has⟩
  | k, _ :: vs, .inr y, a, h => dataAlts_rel d (k + 1) vs y a h
end

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV}

theorem machinesRel_share : (ms : List (MachineV v.records v.event)) → (xs : PerMachine (fun _ => Term) ms) →
    (sms : Step.Machines ms) → MachinesRel M L T ms xs sms → MachinesRel M L T ms (xs.map Term.share) sms
  | [], .nil, .nil, _ => trivial
  | _ :: ms, .cons _ xs, .cons _ sms, h => by
    obtain ⟨h1, h2⟩ := h
    exact ⟨by simpa only [Term.denote_share] using h1, machinesRel_share ms xs sms h2⟩

theorem stateRel_share {shs : List (PendingShape v.event)} {S : SymState v} {s : State v}
    (hR : StateRel M L T shs S s) : StateRel M L T shs S.share s where
  records := by simpa only [SymState.share, Term.denote_share] using hR.records
  now := by simpa only [SymState.share, Term.denote_share] using hR.now
  fresh := by simpa only [SymState.share, Term.denote_share] using hR.fresh
  nextId := by simpa only [SymState.share, Term.denote_share] using hR.nextId
  pending := by simpa only [SymState.share, Term.denote_share] using hR.pending
  machines := machinesRel_share _ _ _ hR.machines

/-- A chain of states chosen by conditions denotes the state of the first condition that holds. -/
theorem foldr_ite_rel {α : Type} {shs : List (PendingShape v.event)} (g : α → Term) (a : α → SymState v)
    (S : SymState v) {s : State v} : (l : List α) → {y : α} →
    l.find? (fun x => ((g x).denote M).toBool) = some y → StateRel M L T shs (a y) s →
    StateRel M L T shs (l.foldr (fun x r => SymState.ite (g x) (a x) r) S) s
  | [], _, h, _ => by cases h
  | x :: l, y, h, hR => by
    rw [List.find?_cons] at h
    simp only [List.foldr_cons]
    split at h
    · rename_i hx
      cases h
      exact stateRel_ite_pos hx _ hR
    · rename_i hx
      exact stateRel_ite_neg (by simpa [Holds] using hx) _ (foldr_ite_rel g a S l h hR)

variable (L T) in
/-- What a model says of an unrolled step from `s` on `x`: it takes a kind whose input decodes to `x` and whose terms
say what the step's result is, the step does not fault, and the state after the step denotes the result's state. -/
def StepAt (M : Model) (hc : v.caller.isData = true) {n : Nat} (st : UnrollStep v n) (s : State v) (x : Input v) :
    Prop :=
  (∃ k ∈ st.kinds, Holds M (st.picks k) ∧ k.1.decode M L hc = some x ∧
    k.2.out.Rel M L T (shapes v) s x (step T v s x)) ∧
  (∀ f, (step T v s x).outcome ≠ .fault f) ∧ StateRel M L T (shapes v) st.after (step T v s x).state

variable (L T) in
/-- A model's unrolled steps from `s` are a run on the inputs `xs`: each step decodes to its input and is that step. -/
def UnrollRun (M : Model) (hc : v.caller.isData = true) {n : Nat} : State v → List (UnrollStep v n) → List (Input v) →
    Prop
  | _, [], [] => True
  | s, st :: sts, x :: xs => st.decode M L hc = some x ∧ StepAt L T M hc st s x ∧
    UnrollRun M hc (step T v s x).state sts xs
  | _, _, _ => False

variable {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (senv : StepEnv L (shapes v))

/-- One unrolled step in a model of its assertions, from terms that denote the run's state `s`, is the step from `s`
on the input it decodes to. -/
theorem unrollOne_at (S : SymState v) (i b : Nat) {s : State v} (hR : StateRel M L T (shapes v) S s)
    (hinv : Step.Inv P s) (hA : ∀ a ∈ (unrollOne L T P v senv S i b).2.1, Holds M a) {x : Input v}
    (hx : (unrollOne L T P v senv S i b).2.2.1.decode M L chk.callerData = some x) :
    StepAt L T M chk.callerData (unrollOne L T P v senv S i b).2.2.1 s x := by
  rcases hp : placeKinds (unrollKinds v (shapes v) senv.nT (i != 0)) (b + 1) with ⟨inps, e⟩
  simp only [unrollOne, hp] at hA hx ⊢
  generalize hoks : (inps.map fun inp => unrollKind L T P v senv S (.var b) inp).filterMap
    (fun | .ok x => some x | .error _ => none) = oks at hA hx ⊢
  have hok : ∀ y ∈ oks, ∃ inp ∈ inps, unrollKind L T P v senv S (.var b) inp = .ok y := fun y hy => by
    rw [← hoks] at hy
    obtain ⟨r, hrm, hro⟩ := List.mem_filterMap.1 hy
    obtain ⟨inp, hi, rfl⟩ := List.mem_map.1 hrm
    refine ⟨inp, hi, ?_⟩
    cases hu : unrollKind L T P v senv S (.var b) inp with
    | error _ => simp [hu] at hro
    | ok x0 => simp [hu] at hro; rw [hro]
  have hpick : ∀ y ∈ oks, y.2.1 = andT (.eq (.var b) (.int y.1.1.pick)) y.1.2.out.case := fun y hy => by
    obtain ⟨inp, -, hu⟩ := hok y hy
    obtain ⟨t, -, -, -, -, -, rfl⟩ := unrollKind_ok senv hu
    rfl
  simp only [UnrollStep.decode, UnrollStep.picks, Option.bind_eq_bind, Option.bind_eq_some_iff] at hx
  obtain ⟨⟨inp, t⟩, hy, hdec⟩ := hx
  rw [List.find?_map] at hy
  obtain ⟨y, hyf, hyeq⟩ := Option.map_eq_some_iff.1 hy
  have hym := List.mem_of_find?_eq_some hyf
  have hyp : Holds M (andT (.eq (.var b) (.int y.1.1.pick)) y.1.2.out.case) := by
    have h := List.find?_some hyf
    simp only [Function.comp_def] at h
    exact h
  obtain ⟨inp', -, hkind⟩ := hok y hym
  obtain ⟨t', valid, wf, henc, -, -, hyv⟩ := unrollKind_ok senv hkind
  have hassert := hA _ (List.mem_append_left _ (List.mem_map_of_mem hym))
  have hfind : oks.find? (fun x => (x.2.1.denote M).toBool) = some y := by
    rw [List.find?_eq_some_iff_append] at hyf ⊢
    obtain ⟨hy1, as, bs, heq, hnot⟩ := hyf
    refine ⟨by rw [hpick y hym]; exact hy1, as, bs, heq, fun a ha => ?_⟩
    rw [hpick a (heq ▸ List.mem_append_left _ ha)]
    exact hnot a ha
  rw [hyv] at hyeq hassert hyp hfind
  simp only at hyeq hyp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hyeq
  simp only at hdec
  simp only [holds_or, holds_not, holds_andT] at hassert
  obtain ⟨-, hcodes, hsites, hcond, hokH, -⟩ := hassert.resolve_left fun h => h ((holds_andT _ _).1 hyp)
  have hcase := ((holds_andT _ _).1 hyp).2
  have ex := step_encode chk senv hR hinv hdec henc
  have hrel := ((ex.2 hcodes hsites hcase).2.1) hcond
  have hafter := after_rel hR hdec hrel
  refine ⟨⟨_, List.mem_map_of_mem (hyv ▸ hym), by simpa [UnrollStep.picks] using hyp, hdec, hrel⟩, hafter.1.1 hokH,
    stateRel_share ?_⟩
  exact foldr_ite_rel (fun x => x.2.1) (fun x => x.2.2.2) S oks hfind (hafter.2 hokH)
end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV}

theorem initTables_rel : (ms : List (MachineV v.records v.event)) → {xs : PerMachine (fun _ => Term) ms} →
    initState.tablesOf L v ms = some xs → MachinesRel M L T ms xs (PerMachine.ofFn (fun _ => []) ms)
  | [], _, h => by cases h; trivial
  | m :: ms, _, h => by
    unfold initState.tablesOf at h
    split at h
    · rename_i k w hm
      obtain ⟨t, ht, h⟩ := bind_some.1 h
      obtain ⟨rest, hrest, rfl⟩ := map_some.1 h
      refine ⟨⟨⟨[], List.Pairwise.nil⟩, ?_, by simp [instancesOf]⟩, initTables_rel ms hrest⟩
      have hnil : (Ty.up m.table m.table_data ⟨[], List.Pairwise.nil⟩).1 = [] := by
        have := Ty.up_table_length m.key (instEntry m.state) m.table_data ⟨[], List.Pairwise.nil⟩
        exact List.eq_nil_of_length_eq_zero this
      obtain ⟨rfl, rfl⟩ : m.key = k ∧ instEntry m.state = w := by
        simp only [MachineV.table, Ty.table.injEq] at hm; exact hm
      refine dataT_rel m.table _ t ?_
      simp only [MachineV.table, dataT] at hnil ⊢
      rw [hnil]
      exact ht
    · rename_i hm; simp [MachineV.table] at hm

/-- The initial state's constants denote the initial state. -/
theorem init_rel {S0 : SymState v} (h : initState L v = some S0) : StateRel M L T (shapes v) S0 (Step.State.init v) := by
  simp only [initState] at h
  obtain ⟨r, hr, h⟩ := bind_some.1 h
  obtain ⟨p, hp, h⟩ := bind_some.1 h
  obtain ⟨tables, ht, h⟩ := bind_some.1 h
  cases h
  refine ⟨dataT_rel _ _ r hr, rfl, rfl, rfl, ⟨⟨[], List.Pairwise.nil⟩, dataT_rel (pendingTable (shapes v)) _ p ?_, .nil⟩,
    initTables_rel v.machines ht⟩
  simpa [dataT, pendingTable] using hp

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV} {P : List AnySite} {E : List AnyEffectSite}
  (chk : Checked P E T v) (senv : StepEnv L (shapes v))

theorem unrollSteps_run : (d : Nat) → (S : SymState v) → (i b : Nat) → {s : State v} →
    StateRel M L T (shapes v) S s → Step.Inv P s → (∀ a ∈ (unrollSteps L T P v senv S i b d).2.1, Holds M a) →
    (∀ st ∈ (unrollSteps L T P v senv S i b d).2.2.1, ∃ x, st.decode M L chk.callerData = some x) →
    ∃ xs, UnrollRun L T M chk.callerData s (unrollSteps L T P v senv S i b d).2.2.1 xs
  | 0, _, _, _, _, _, _, _, _ => ⟨[], trivial⟩
  | d + 1, S, i, b, s, hR, hinv, hA, hD => by
    rcases h1 : unrollOne L T P v senv S i b with ⟨tys, asserts, st0, refused, b'⟩
    rcases h2 : unrollSteps L T P v senv st0.after (i + 1) b' d with ⟨tys', asserts', sts, refused'⟩
    simp only [unrollSteps, h1, h2] at hA hD ⊢
    obtain ⟨x, hx⟩ := hD st0 (List.mem_cons_self ..)
    have hat := unrollOne_at chk senv S i b hR hinv (by rw [h1]; exact fun a ha => hA a (List.mem_append_left _ ha))
      (by rw [h1]; exact hx)
    rw [h1] at hat
    have ih := unrollSteps_run d st0.after (i + 1) b' hat.2.2 (step_inv T chk.reach s hinv x)
      (by rw [h2]; exact fun a ha => hA a (List.mem_append_right _ ha))
      (by rw [h2]; exact fun st hst => hD st (List.mem_cons_of_mem _ hst))
    rw [h2] at ih
    obtain ⟨xs, hxs⟩ := ih
    exact ⟨x :: xs, hx, hat, hxs⟩

/-- A model of an unrolled run is a run: in every model of the script whose variables hold values of their sorts,
the steps decode to inputs whose run from the initial state takes, at each step, a kind whose terms say what the step
is, faults nowhere, and leaves the state the step's end terms denote. So generate's playback of a model always
replays, and its "does not decode" line is unreachable. -/
theorem unroll_decode {d : Nat} {goal : List (UnrollStep v senv.nT) → Term} {U : Unrolled v senv.nT}
    (hu : unroll L T P v senv d goal = .ok U)
    (hM : ∀ n (h : n < U.ask.tys.length), VarSorted L U.ask.tys[n] (M.vars n)) (hA : ∀ a ∈ U.ask.asserts, Holds M a) :
    ∃ xs, UnrollRun L T M chk.callerData (Step.State.init v) U.steps xs := by
  have hD := unroll_inputs_decode senv chk.callerData hu hM hA
  simp only [unroll] at hu
  obtain ⟨S0, hS0, hu⟩ := bind_ok.1 hu
  obtain ⟨dts, -, hu⟩ := bind_ok.1 hu
  rcases hr : unrollSteps L T P v senv S0 0 0 d with ⟨tys, asserts, steps, refused⟩
  rw [hr] at hu
  obtain ⟨vars, -, hu⟩ := bind_ok.1 hu
  cases pure_ok.1 hu
  have h := unrollSteps_run chk senv d S0 0 0 (init_rel (need_ok.1 hS0)) Step.init_inv
    (by rw [hr]; exact fun a ha => hA a (List.mem_append_left _ ha)) (by rw [hr]; exact hD)
  rw [hr] at h
  exact h

end

end Tazuna.Smt
