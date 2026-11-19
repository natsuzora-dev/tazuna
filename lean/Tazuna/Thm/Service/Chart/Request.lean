import Tazuna.Service.Chart.Request
import Tazuna.Thm.Service.Chart.Queue

namespace Tazuna.Thm.Service.Chart.Request

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Functions Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem keeps_request (step : Nat) (name : InstanceId) (state : String) (a : Activity) : Keeps (request fs st step name state a) := by
  unfold request
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  split
  · simp [Processing.report]
  · split
    · rfl
    · exact await_fixed ..

theorem keeps_openScreen (step : Nat) (name : InstanceId) (state : String) (a : Activity) :
    Keeps (openScreen fs st step name state a) := by
  unfold openScreen
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  repeat' split
  all_goals first | rfl | simp [Processing.report]

theorem keeps_activate (step : Nat) (name : InstanceId) (state : String) (a : Activity) :
    Keeps (activate fs st step name state a) := by
  unfold activate
  split
  · exact keeps_openScreen step name state _
  · intro r; rfl
  · exact keeps_request step name state _
  · exact keeps_request step name state _

theorem growsBy_request (step : Nat) (name : InstanceId) (state : String) (a : Activity) : GrowsBy (request fs st step name state a) := by
  unfold request
  apply growsBy_withMachine
  intro i r
  try simp only [id_bind]
  split
  · exact Grows.of_lines (report_lines ..)
  · split
    · exact Grows.refl _
    · refine ⟨#[_], Array.push_eq_append, ?_⟩
      simp [State.createKeys]

theorem sameLines_openScreen (step : Nat) (name : InstanceId) (state : String) (a : Activity) :
    SameLines (openScreen fs st step name state a) := by
  unfold openScreen
  apply sameLines_withMachine
  intro i r
  try simp only [id_bind]
  repeat' split
  all_goals first | rfl | simp [Processing.report]

theorem growsBy_activate (step : Nat) (name : InstanceId) (state : String) (a : Activity) :
    GrowsBy (activate fs st step name state a) := by
  unfold activate
  split
  · exact (sameLines_openScreen step name state _).grows
  · intro r; exact Grows.refl _
  · exact growsBy_request step name state _
  · exact growsBy_request step name state _

theorem keeps_activateEntered (e : InstanceId × String × Nat) : Keeps (activateEntered fs st e) := by
  unfold activateEntered
  apply keeps_withMachine
  intro i r
  split
  · rfl
  · split
    · rfl
    · exact foldlM_keeps (fun a => keeps_unlessHalted (keeps_activate _ _ _ a)) _ _

theorem keeps_sendEntered : Keeps (sendEntered fs st) := fun r =>
  foldlM_keeps (fun e => keeps_activateEntered e) _ ⟨r.state, { r.queue with entered := [] }⟩

theorem growsBy_activateEntered (e : InstanceId × String × Nat) : GrowsBy (activateEntered fs st e) := by
  unfold activateEntered
  apply growsBy_withMachine
  intro i r
  split
  · exact Grows.refl _
  · split
    · exact Grows.refl _
    · exact (foldlM_grows (fun a => growsBy_unlessHalted (growsBy_activate _ _ _ a))
        (fun a => keeps_unlessHalted (keeps_activate _ _ _ a)) _ _).bridge rfl rfl

theorem growsBy_sendEntered : GrowsBy (sendEntered fs st) := fun r =>
  (foldlM_grows (fun e => growsBy_activateEntered e) (fun e => keeps_activateEntered e) _
    ⟨r.state, { r.queue with entered := [] }⟩).bridge rfl rfl

theorem exited_state_sends_nothing (e : InstanceId × String × Nat) (r : Processing) (i : Instance)
    (hi : r.state.machine? e.1 = some i) (hn : i.isIn e.2.1 = false) : activateEntered fs st e r = r := by
  unfold activateEntered withMachine
  split
  · rfl
  · simp [hi, hn]

theorem entering_opens_one_child (step : Nat) (name : InstanceId) (state : String) (a : Activity) (r : Processing) (i : Instance)
    (c : Chart) (given : Value) (keys : List String) (context : Value) (hh : r.state.halted = none)
    (hi : r.state.machine? name = some i) (hc : st.chart? a.ref.name = some c)
    (raw : Value) (hp : fs.input (r.state.scopeOf i (some state)) r.state.records a r.state.nextKeys = .ok (raw, keys))
    (hq : fs.parse (.input (st.ref c.name)) raw = .ok (some given))
    (hr : firstFalse (fs.inputRequirement (st.ref c.name) · given) (st.requirementsOf c.name).requires = .ok none)
    (hx : fs.initialContext c.name given = .ok context) :
    ∃ child : Instance, (openScreen fs st step name state a r).1.machines = r.state.machines ++ [child] ∧
      child.chart = c ∧ child.id.opener? = some (name, state, a.key) ∧ child.modal = a.isModal ∧
      (openScreen fs st step name state a r).1.stack = r.state.stack ++ [child.id] ∧
      (openScreen fs st step name state a r).2.tasks = r.queue.tasks ++ [.start child.id (some step)] := by
  simp only [openScreen, withMachine, Processing.halted, hh, hi, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, id_bind,
    hc, hp, hq, hr, initialContextOf, hx]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

def EnteredFrom (s s' : State) : Prop :=
  ∀ n i', s'.machine? n = some i' → i'.entered = [] ∨ ∃ i, s.machine? n = some i ∧ i.closed = i'.closed ∧ i.entered = i'.entered

theorem EnteredFrom.append {s s' : State} (c : Instance) (hc : c.entered = []) (hm : s'.machines = s.machines ++ [c])
    (hk : s'.copies = s.copies) : EnteredFrom s s' := by
  intro n i' h
  simp only [State.machine?, hm, hk, List.append_assoc, List.find?_append] at h
  simp only [State.machine?, List.find?_append]
  cases hs : s.machines.find? (·.id == n) with
  | some x =>
    rw [hs] at h
    obtain rfl : x = i' := by simpa using h
    exact .inr ⟨x, rfl, rfl, rfl⟩
  | none =>
    rw [hs] at h
    cases hcf : [c].find? (·.id == n) with
    | some y =>
      rw [hcf] at h
      have : y = c := by simp only [List.find?] at hcf; split at hcf <;> simp_all
      simp only [Option.some_or, Option.or_some, Option.getD_none, Option.some.injEq] at h
      exact .inl (h ▸ this ▸ hc)
    | none => rw [hcf] at h; exact .inr ⟨i', by simpa using h, rfl, rfl⟩

theorem EnteredFrom.active {s s' : State} (h : EnteredFrom s s') {name : InstanceId} {n : String} {i' : Instance}
    (hi : s'.machine? name = some i') (hc : i'.closed = false) (hn : i'.isIn n = true) :
    ∃ i, s.machine? name = some i ∧ i.closed = false ∧ i.isIn n = true := by
  rcases h name i' hi with he | ⟨i, h, hc', he⟩
  · simp [Instance.isIn, he] at hn
  · exact ⟨i, h, hc'.trans hc, by simpa [Instance.isIn, he] using hn⟩

end Tazuna.Thm.Service.Chart.Request
