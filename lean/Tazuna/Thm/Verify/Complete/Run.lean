import Tazuna.Thm.Verify.Complete.Values

namespace Tazuna.Thm.Verify.Complete.Run

open Tazuna.Data Tazuna.Verify
open Tazuna.Thm.Verify.Complete.Values

/-- The result and the final state of `a`. -/
def run {α : Type} (a : CompareM α) (c : Ctx) (st : St) : α × St := (a.run c).run st

theorem run_bind {α β : Type} (a : CompareM α) (f : α → CompareM β) (c : Ctx) (st : St) :
    run (a >>= f) c st = run (f (run a c st).1) c (run a c st).2 := rfl

theorem run_pure {α : Type} (x : α) (c : Ctx) (st : St) : run (pure x : CompareM α) c st = (x, st) := rfl

theorem run_get (c : Ctx) (st : St) : run (get : CompareM St) c st = (st, st) := rfl

theorem run_set (s : St) (c : Ctx) (st : St) : run (set s : CompareM PUnit) c st = (⟨⟩, s) := rfl

theorem run_report (m : Mismatch) (c : Ctx) (st : St) :
    run (report m) c st = (⟨⟩, { st with findings := st.findings ++ [m] }) := rfl

theorem run_modify (f : St → St) (c : Ctx) (st : St) :
    run (modify f : CompareM PUnit) c st = (⟨⟩, f st) := rfl

theorem run_bind_get {β : Type} (f : St → CompareM β) (c : Ctx) (st : St) :
    run (get >>= f) c st = run (f st) c st := rfl

theorem run_bind_read {β : Type} (f : Ctx → CompareM β) (c : Ctx) (st : St) :
    run (read >>= f) c st = run (f c) c st := rfl

theorem run_bind_set {β : Type} (s : St) (f : PUnit → CompareM β) (c : Ctx) (st : St) :
    run (set s >>= f) c st = run (f ⟨⟩) c s := rfl

theorem run_bind_modify {β : Type} (g : St → St) (f : PUnit → CompareM β) (c : Ctx) (st : St) :
    run (modify g >>= f) c st = run (f ⟨⟩) c (g st) := rfl

theorem run_bind_report {β : Type} (m : Mismatch) (f : PUnit → CompareM β) (c : Ctx) (st : St) :
    run (report m >>= f) c st = run (f ⟨⟩) c { st with findings := st.findings ++ [m] } := rfl

theorem run_bind_pure {α β : Type} (x : α) (f : α → CompareM β) (c : Ctx) (st : St) :
    run (pure x >>= f) c st = run (f x) c st := rfl

theorem run_map {α β : Type} (f : α → β) (a : CompareM α) (c : Ctx) (st : St) :
    run (f <$> a) c st = (f (run a c st).1, (run a c st).2) := rfl

theorem run_ite {α : Type} (p : Prop) [Decidable p] (a b : CompareM α) (c : Ctx) (st : St) :
    run (if p then a else b) c st = if p then run a c st else run b c st := by
  split <;> rfl

/-- Steps through binds of state and context accesses, so that a read state stays the same term everywhere. -/
macro "simp_run" : tactic =>
  `(tactic| simp only [run_bind_get, run_bind_read, run_bind_set, run_bind_modify, run_bind_report, run_bind_pure,
    run_ite, run_pure, run_report, run_modify, run_map])

theorem run_forIn_cons {α β : Type} (x : α) (xs : List α) (b : β) (f : α → β → CompareM (ForInStep β))
    (c : Ctx) (st : St) :
    run (forIn (x :: xs) b f) c st =
      match run (f x b) c st with
      | (.yield b', st') => run (forIn xs b' f) c st'
      | (.done b', st') => (b', st') := by
  simp only [run, List.forIn_cons]
  simp only [bind, ReaderT.bind, StateT.bind, ReaderT.run, StateT.run]
  rcases (f x b c st) with ⟨r, st'⟩
  cases r <;> rfl

/-- An invariant of a loop whose every step yields, over the processed prefix of the list. -/
theorem forIn_induct {α β : Type} (xs : List α) (init : β) (f : α → β → CompareM (ForInStep β)) (c : Ctx)
    (st : St) (P : List α → β → St → Prop) (hy : ∀ x b st, ∃ b', (run (f x b) c st).1 = .yield b')
    (hs : ∀ pre x b st, pre ++ [x] <+: xs → P pre b st →
      P (pre ++ [x]) (run (f x b) c st).1.value (run (f x b) c st).2)
    (h0 : P [] init st) : P xs (run (forIn xs init f) c st).1 (run (forIn xs init f) c st).2 := by
  suffices ∀ (rest pre : List α) (b : β) (st : St), pre ++ rest = xs → P pre b st →
      P xs (run (forIn rest b f) c st).1 (run (forIn rest b f) c st).2 from this xs [] init st (by simp) h0
  intro rest
  induction rest with
  | nil => intro pre b st e h; simp only [List.append_nil] at e; subst e; exact h
  | cons x rest ih =>
    intro pre b st e h
    rw [run_forIn_cons]
    obtain ⟨b', hb⟩ := hy x b st
    have hstep := hs pre x b st ⟨rest, by simp [← e]⟩ h
    rw [hb] at hstep
    rw [show run (f x b) c st = (.yield b', (run (f x b) c st).2) from Prod.ext hb rfl]
    exact ih (pre ++ [x]) b' _ (by simp [← e]) hstep

/-- `forIn_induct` for a goal about the result of the loop. -/
theorem forIn_apply {α β : Type} (xs : List α) (init : β) (f : α → β → CompareM (ForInStep β)) (c : Ctx)
    (st : St) (P : List α → β → St → Prop) (Q : β × St → Prop) (hy : ∀ x b st, ∃ b', (run (f x b) c st).1 = .yield b')
    (hs : ∀ pre x b st, pre ++ [x] <+: xs → P pre b st →
      P (pre ++ [x]) (run (f x b) c st).1.value (run (f x b) c st).2)
    (h0 : P [] init st) (hQ : ∀ r : β × St, P xs r.1 r.2 → Q r) : Q (run (forIn xs init f) c st) :=
  hQ _ (forIn_induct xs init f c st P hy hs h0)

/-- `forIn_induct` for a named result of the loop. -/
theorem forIn_eq_induct {α β : Type} {xs : List α} {init : β} {f : α → β → CompareM (ForInStep β)} {c : Ctx}
    {st : St} (P : List α → β → St → Prop) (hy : ∀ x b st, ∃ b', (run (f x b) c st).1 = .yield b')
    (hs : ∀ pre x b st, pre ++ [x] <+: xs → P pre b st →
      P (pre ++ [x]) (run (f x b) c st).1.value (run (f x b) c st).2)
    (h0 : P [] init st) {L : β × St} (hL : run (forIn xs init f) c st = L) : P xs L.1 L.2 :=
  hL ▸ forIn_induct xs init f c st P hy hs h0

/-- A loop whose every step either leaves the state alone with `good` holding, or reports. -/
theorem forIn_checks {α : Type} {xs : List α} {f : α → PUnit → CompareM (ForInStep PUnit)} {c : Ctx} {st : St}
    (good : α → Prop)
    (hf : ∀ x st, (run (f x ⟨⟩) c st).1 = .yield ⟨⟩ ∧
      ((run (f x ⟨⟩) c st).2 = st ∧ good x ∨ ∃ m, (run (f x ⟨⟩) c st).2.findings = st.findings ++ [m]))
    {L : PUnit × St} (hL : run (forIn xs ⟨⟩ f) c st = L) :
    st.findings <+: L.2.findings ∧ (L.2.findings = st.findings → L.2 = st ∧ ∀ x ∈ xs, good x) := by
  refine forIn_eq_induct (fun pre _ st' => st.findings <+: st'.findings ∧
    (st'.findings = st.findings → st' = st ∧ ∀ x ∈ pre, good x)) (fun x b st => ⟨⟨⟩, (hf x st).1⟩) ?_
    ⟨List.prefix_refl _, fun _ => ⟨rfl, by simp⟩⟩ hL
  rintro pre x ⟨⟩ st' _ ⟨hp, hq⟩
  rcases (hf x st').2 with ⟨he, hg⟩ | ⟨m, hm⟩
  · rw [he]
    refine ⟨hp, fun e => ?_⟩
    obtain ⟨h1, h2⟩ := hq e
    exact ⟨h1, fun y hy => by
      rcases List.mem_append.mp hy with hy | hy
      · exact h2 y hy
      · simp only [List.mem_singleton] at hy; subst hy; exact hg⟩
  · rw [hm]
    refine ⟨hp.trans (List.prefix_append _ _), fun e => ?_⟩
    have := congrArg List.length e
    have := hp.length_le
    simp at *; omega

theorem prefix_antisymm {α : Type} {a b : List α} (h₁ : a <+: b) (h₂ : b <+: a) : a = b :=
  h₁.eq_of_length (Nat.le_antisymm h₁.length_le h₂.length_le)

theorem prefix_squeeze {α : Type} {a b c : List α} (h₁ : a <+: b) (h₂ : b <+: c) (h : c = a) : b = a :=
  (prefix_antisymm h₁ (h ▸ h₂)).symm

/-- The ids after a paired line: an answer binds the request that it answers. -/
def idsAfter (s : Line) (t : Out) (ids : Ids) : Ids :=
  match s.body with
  | .answer _ _ to _ => ids.bind (some to) t.line.body.to?
  | _ => ids

/-- The state after `matchLine s t`, apart from findings. -/
theorem matchLine_run (s : Line) (t : Out) (c : Ctx) (st : St) :
    let st' := (run (matchLine s t) c st).2
    st.findings <+: st'.findings ∧
      st'.values = (tryEqual st.declared (c.compared s t.line).1 (c.compared s t.line).2 st.values).2 ∧
      st'.ids = idsAfter s t st.ids ∧
      st'.declared = st.declared ∧ st'.openSnapshot = st.openSnapshot ∧ st'.openTrace = st.openTrace ∧
      st'.subscriptionIds = st.subscriptionIds ∧ st'.reportedMissing = st.reportedMissing ∧
      st'.reportedUnexpected = st.reportedUnexpected ∧
      (st'.findings = st.findings → (∀ m, valueMismatch c s t m ≠ none) →
        sameTime s t.line = true ∧
          (tryEqual st.declared (c.compared s t.line).1 (c.compared s t.line).2 st.values).1 = true) := by
  simp only [matchLine]
  simp_run
  generalize valueMismatch c s t = vm
  split <;> split <;> simp_run <;> split <;> (try split) <;>
    (try rename_i hx; have := Option.eq_none_iff_forall_ne_some.mpr hx) <;>
    (simp_all [List.prefix_append, idsAfter, run_pure, run_report] <;> exact ⟨_, this⟩)

end Tazuna.Thm.Verify.Complete.Run
