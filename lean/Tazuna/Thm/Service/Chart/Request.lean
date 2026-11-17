import Tazuna.Service.Chart.Request
import Tazuna.Thm.Service.Chart.Queue

namespace Tazuna.Thm.Service.Chart.Request

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Chart.Queue Tazuna.Thm.Service.Functions Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem initialContextOf_error_halts (chart : String) (input : Value) (v : Fault)
    (h : initialContextOf fs st chart input = .error v) : v.halts = true := by
  unfold initialContextOf at h
  simp only [id_bind] at h
  split at h
  · injection h with h
    rw [← h]
    exact issueViolation_halts _ _ _ fun _ => rfl
  · cases h

theorem keeps_request (step : Nat) (name state : String) (a : Activity) : Keeps (request fs st step name state a) := by
  unfold request
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  split
  · simp [Processing.report]
  · split
    · rfl
    · exact await_fixed ..

theorem keeps_openScreen (step : Nat) (name state : String) (a : Activity) :
    Keeps (openScreen fs st step name state a) := by
  unfold openScreen
  apply keeps_withMachine
  intro i r
  try simp only [id_bind]
  repeat' split
  all_goals first | rfl | simp [Processing.report]

theorem keeps_activate (step : Nat) (name state : String) (a : Activity) :
    Keeps (activate fs st step name state a) := by
  unfold activate
  split
  · exact keeps_openScreen step name state _
  · intro r; rfl
  · exact keeps_request step name state _
  · exact keeps_request step name state _

theorem growsBy_request (step : Nat) (name state : String) (a : Activity) : GrowsBy (request fs st step name state a) := by
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

theorem sameLines_openScreen (step : Nat) (name state : String) (a : Activity) :
    SameLines (openScreen fs st step name state a) := by
  unfold openScreen
  apply sameLines_withMachine
  intro i r
  try simp only [id_bind]
  repeat' split
  all_goals first | rfl | simp [Processing.report]

theorem growsBy_activate (step : Nat) (name state : String) (a : Activity) :
    GrowsBy (activate fs st step name state a) := by
  unfold activate
  split
  · exact (sameLines_openScreen step name state _).grows
  · intro r; exact Grows.refl _
  · exact growsBy_request step name state _
  · exact growsBy_request step name state _

theorem keeps_activateEntered (e : String × String × Nat) : Keeps (activateEntered fs st e) := by
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

theorem growsBy_activateEntered (e : String × String × Nat) : GrowsBy (activateEntered fs st e) := by
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

theorem exited_state_sends_nothing (e : String × String × Nat) (r : Processing) (i : Instance)
    (hi : r.state.machine? e.1 = some i) (hn : i.isIn e.2.1 = false) : activateEntered fs st e r = r := by
  unfold activateEntered withMachine
  split
  · rfl
  · simp [hi, hn]

theorem activate_opens (step : Nat) (name state key : String) (target : Spec.Ref) (modal : Bool) :
    activate fs st step name state (.opens key target modal) = openScreen fs st step name state (.opens key target modal) :=
  rfl

theorem entering_opens_one_child (step : Nat) (name state : String) (a : Activity) (r : Processing) (i : Instance)
    (c : Chart) (given : Value) (keys : List String) (context : Value) (hh : r.state.halted = none)
    (hi : r.state.machine? name = some i) (hc : st.chart? a.ref.name = some c)
    (raw : Value) (hp : fs.input (r.state.scopeOf i (some state)) r.state.records a r.state.nextKeys = .ok (raw, keys))
    (hq : fs.parse (.input c.name) raw = .ok (some given))
    (hr : firstFalse (fs.inputRequirement c.name · given) (st.requirementsOf c.name).requires = .ok none)
    (hx : fs.initialContext c.name given = .ok context) :
    ∃ child : Instance, (openScreen fs st step name state a r).1.machines = r.state.machines ++ [child] ∧
      child.chart = c ∧ child.opener = some { parent := name, state, key := a.key, modal := a.isModal } ∧
      (openScreen fs st step name state a r).1.stack = r.state.stack ++ [child.resource] ∧
      (openScreen fs st step name state a r).2.tasks = r.queue.tasks ++ [.start child.resource (some step)] := by
  simp only [openScreen, withMachine, Processing.halted, hh, hi, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, id_bind,
    hc, hp, hq, hr, initialContextOf, hx]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem requests_wait_in_send_order (step : Nat) (name state : String) (a : Activity) (r : Processing) (i : Instance)
    (input : Value) (keys : List String) (hh : r.state.halted = none) (hi : r.state.machine? name = some i)
    (ho : a.isOwn st.service = false) (hp : fs.input (r.state.scopeOf i (some state)) r.state.records a r.state.nextKeys = .ok (input, keys)) :
    ∃ p, (request fs st step name state a r).1.pending = r.state.pending ++ [p] ∧ p.activity = a ∧ p.requester = .state name state ∧
      p.input = input ∧ p.turn = r.state.turn ∧ (request fs st step name state a r).1.turn = r.state.turn + 1 := by
  refine ⟨{ id := ((r.state.createKeys keys).write .out none (a.requestLine (st.traceNameOf a.ref) input)).2,
             activity := a, requester := .state name state, input := input, turn := r.state.turn }, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp only [request, withMachine, Processing.halted, hh, hi, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, id_bind,
      hp, ho]
    rfl
  · simp only [request, withMachine, Processing.halted, hh, hi, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, id_bind,
      hp, ho]
    rfl

def AddsFor (name state : String) (f : Processing → Id Processing) : Prop :=
  ∀ r, (∀ p ∈ (f r).1.pending, p ∉ r.state.pending → p.requester = .state name state) ∧
    ∀ c ∈ (f r).1.machines, c ∉ r.state.machines → c.opener.map (fun o => (o.parent, o.state)) = some (name, state)

theorem addsFor_request (step : Nat) (name state : String) (a : Activity) : AddsFor name state (request fs st step name state a) := by
  intro r
  unfold request withMachine
  split
  · exact ⟨fun _ h h' => absurd h h', fun _ h h' => absurd h h'⟩
  · split
    · simp only [id_bind]
      split
      · exact ⟨fun _ h h' => absurd (by simpa [Processing.report] using h) h',
          fun _ h h' => absurd (by simpa [Processing.report] using h) h'⟩
      · split
        · exact ⟨fun _ h h' => absurd h h', fun _ h h' => absurd h h'⟩
        · refine ⟨fun p hp hn => ?_, fun c hc hn => absurd hc hn⟩
          rcases List.mem_append.mp hp with hp | hp
          · exact absurd hp hn
          · rw [List.mem_singleton.mp hp]
    · exact ⟨fun _ h h' => absurd h h', fun _ h h' => absurd h h'⟩

theorem addsFor_openScreen (step : Nat) (name state : String) (a : Activity) :
    AddsFor name state (openScreen fs st step name state a) := by
  intro r
  unfold openScreen withMachine
  try simp only [id_bind]
  repeat' split
  all_goals first
    | exact ⟨fun _ h h' => absurd h h', fun _ h h' => absurd h h'⟩
    | exact ⟨fun _ h h' => absurd (by simpa [Processing.report] using h) h',
        fun _ h h' => absurd (by simpa [Processing.report] using h) h'⟩
    | (refine ⟨fun p hp hn => absurd hp hn, fun c hc hn => ?_⟩
       rcases List.mem_append.mp hc with hc | hc
       · exact absurd hc hn
       · rw [List.mem_singleton.mp hc]; rfl)

theorem addsFor_activate (step : Nat) (name state : String) (a : Activity) :
    AddsFor name state (activate fs st step name state a) := by
  unfold activate
  split
  · exact addsFor_openScreen step name state _
  · intro r; exact ⟨fun _ h h' => absurd h h', fun _ h h' => absurd h h'⟩
  · exact addsFor_request step name state _
  · exact addsFor_request step name state _

theorem addsFor_foldlM {α : Type} {name state : String} {g : α → Processing → Id Processing}
    (h : ∀ x, AddsFor name state (g x)) (xs : List α) :
    AddsFor name state (fun r => xs.foldlM (fun r x => unlessHalted (g x) r) r) := by
  induction xs with
  | nil => intro r; exact ⟨fun _ h h' => absurd h h', fun _ h h' => absurd h h'⟩
  | cons x xs ih =>
    intro r
    simp only [List.foldlM_cons, id_bind]
    have h1 : AddsFor name state (unlessHalted (g x)) := by
      intro r
      unfold unlessHalted
      split
      · exact ⟨fun _ h h' => absurd h h', fun _ h h' => absurd h h'⟩
      · exact h x r
    obtain ⟨ip, ic⟩ := ih (unlessHalted (g x) r)
    obtain ⟨fp, fc⟩ := h1 r
    refine ⟨fun p hp hn => ?_, fun c hc hn => ?_⟩
    · by_cases hm : p ∈ (unlessHalted (g x) r).state.pending
      · exact fp p hm hn
      · exact ip p hp hm
    · by_cases hm : c ∈ (unlessHalted (g x) r).state.machines
      · exact fc c hm hn
      · exact ic c hc hm

theorem activateEntered_adds_for_active (e : String × String × Nat) (r : Processing) :
    (∀ p ∈ (activateEntered fs st e r).1.pending, p ∉ r.state.pending →
      p.requester = .state e.1 e.2.1 ∧ ∃ i, r.state.machine? e.1 = some i ∧ i.closed = false ∧ i.isIn e.2.1 = true) ∧
    ∀ c ∈ (activateEntered fs st e r).1.machines, c ∉ r.state.machines →
      c.opener.map (fun o => (o.parent, o.state)) = some (e.1, e.2.1) ∧
        ∃ i, r.state.machine? e.1 = some i ∧ i.closed = false ∧ i.isIn e.2.1 = true := by
  unfold activateEntered withMachine
  split
  · exact ⟨fun _ h h' => absurd h h', fun _ h h' => absurd h h'⟩
  · split
    · rename_i i hi
      simp only []
      split
      · exact ⟨fun _ h h' => absurd h h', fun _ h h' => absurd h h'⟩
      · rename_i hact
        have hc : i.closed = false ∧ i.isIn e.2.1 = true := by simpa using hact
        split
        · exact ⟨fun _ h h' => absurd h h', fun _ h h' => absurd h h'⟩
        · obtain ⟨fp, fc⟩ := addsFor_foldlM (fun a => addsFor_activate (fs := fs) (st := st) _ e.1 e.2.1 a) _
            ⟨(r.state.newStep (some e.2.2) true).1, r.queue⟩
          exact ⟨fun p hp hn => ⟨fp p hp hn, i, hi, hc⟩,
            fun c hm hn => ⟨fc c hm hn, i, hi, hc⟩⟩
    · exact ⟨fun _ h h' => absurd h h', fun _ h h' => absurd h h'⟩

def EnteredFrom (s s' : State) : Prop :=
  ∀ n i', s'.machine? n = some i' → i'.entered = [] ∨ ∃ i, s.machine? n = some i ∧ i.closed = i'.closed ∧ i.entered = i'.entered

theorem EnteredFrom.refl (s : State) : EnteredFrom s s := fun _ i' h => .inr ⟨i', h, rfl, rfl⟩

theorem EnteredFrom.trans {a b c : State} (h₁ : EnteredFrom a b) (h₂ : EnteredFrom b c) : EnteredFrom a c := by
  intro n i'' h
  rcases h₂ n i'' h with h | ⟨i', h', hc, he⟩
  · exact .inl h
  · rcases h₁ n i' h' with h | ⟨i, h, hc', he'⟩
    · exact .inl (he ▸ h)
    · exact .inr ⟨i, h, hc'.trans hc, he'.trans he⟩

theorem EnteredFrom.of_machines {s s' : State} (hm : s'.machines = s.machines) (hc : s'.copies = s.copies) :
    EnteredFrom s s' := fun n i' h => .inr ⟨i', by simpa [State.machine?, hm, hc] using h, rfl, rfl⟩

theorem EnteredFrom.append {s s' : State} (c : Instance) (hc : c.entered = []) (hm : s'.machines = s.machines ++ [c])
    (hk : s'.copies = s.copies) : EnteredFrom s s' := by
  intro n i' h
  simp only [State.machine?, hm, hk, List.append_assoc, List.find?_append] at h
  simp only [State.machine?, List.find?_append]
  cases hs : s.machines.find? (·.resource == n) with
  | some x =>
    rw [hs] at h
    obtain rfl : x = i' := by simpa using h
    exact .inr ⟨x, rfl, rfl, rfl⟩
  | none =>
    rw [hs] at h
    cases hcf : [c].find? (·.resource == n) with
    | some y =>
      rw [hcf] at h
      have : y = c := by simp only [List.find?] at hcf; split at hcf <;> simp_all
      simp only [Option.some_or, Option.or_some, Option.getD_none, Option.some.injEq] at h
      exact .inl (h ▸ this ▸ hc)
    | none => rw [hcf] at h; exact .inr ⟨i', by simpa using h, rfl, rfl⟩

def KeepsEntered (f : Processing → Id Processing) : Prop := ∀ r, EnteredFrom r.state (f r).1

theorem keepsEntered_unlessHalted {f : Processing → Id Processing} (h : KeepsEntered f) : KeepsEntered (unlessHalted f) := by
  intro r
  unfold unlessHalted
  split
  · exact EnteredFrom.refl _
  · exact h r

theorem keepsEntered_foldlM {α : Type} {g : α → Processing → Id Processing} (h : ∀ x, KeepsEntered (g x)) (xs : List α) :
    KeepsEntered (fun r => xs.foldlM (fun r x => g x r) r) := by
  induction xs with
  | nil => intro r; exact EnteredFrom.refl _
  | cons x xs ih => intro r; exact (h x r).trans (ih (g x r))

theorem keepsEntered_request (step : Nat) (name state : String) (a : Activity) :
    KeepsEntered (request fs st step name state a) := by
  intro r
  unfold request withMachine
  split
  · exact EnteredFrom.refl _
  · split
    · simp only [id_bind]
      split
      · exact EnteredFrom.of_machines (by simp [Processing.report]) (by simp [Processing.report])
      · split
        · exact EnteredFrom.of_machines rfl rfl
        · exact EnteredFrom.of_machines rfl rfl
    · exact EnteredFrom.refl _

theorem keepsEntered_openScreen (step : Nat) (name state : String) (a : Activity) :
    KeepsEntered (openScreen fs st step name state a) := by
  intro r
  unfold openScreen withMachine
  split
  · exact EnteredFrom.refl _
  · split
    · split
      · exact EnteredFrom.refl _
      · simp only [id_bind]
        split
        · exact EnteredFrom.of_machines (by simp [Processing.report]) (by simp [Processing.report])
        · split
          · exact EnteredFrom.of_machines (by simp [Processing.report]) (by simp [Processing.report])
          · exact EnteredFrom.of_machines (by simp [Processing.report]) (by simp [Processing.report])
          · split
            · exact EnteredFrom.of_machines (by simp [Processing.report]) (by simp [Processing.report])
            · exact EnteredFrom.of_machines (by simp [Processing.report]) (by simp [Processing.report])
            · split
              · exact EnteredFrom.of_machines (by simp [Processing.report]) (by simp [Processing.report])
              · exact EnteredFrom.append _ rfl rfl rfl
    · exact EnteredFrom.refl _

theorem keepsEntered_activate (step : Nat) (name state : String) (a : Activity) :
    KeepsEntered (activate fs st step name state a) := by
  unfold activate
  split
  · exact keepsEntered_openScreen step name state _
  · intro r; exact EnteredFrom.refl _
  · exact keepsEntered_request step name state _
  · exact keepsEntered_request step name state _

theorem keepsEntered_activateEntered (e : String × String × Nat) : KeepsEntered (activateEntered fs st e) := by
  intro r
  unfold activateEntered withMachine
  split
  · exact EnteredFrom.refl _
  · split
    · simp only []
      split
      · exact EnteredFrom.refl _
      · split
        · exact EnteredFrom.refl _
        · exact (EnteredFrom.of_machines rfl rfl).trans
            (keepsEntered_foldlM (fun a => keepsEntered_unlessHalted (keepsEntered_activate _ e.1 e.2.1 a)) _ _)
    · exact EnteredFrom.refl _

theorem EnteredFrom.active {s s' : State} (h : EnteredFrom s s') {name n : String} {i' : Instance}
    (hi : s'.machine? name = some i') (hc : i'.closed = false) (hn : i'.isIn n = true) :
    ∃ i, s.machine? name = some i ∧ i.closed = false ∧ i.isIn n = true := by
  rcases h name i' hi with he | ⟨i, h, hc', he⟩
  · simp [Instance.isIn, he] at hn
  · exact ⟨i, h, hc'.trans hc, by simpa [Instance.isIn, he] using hn⟩

theorem sendEntered_adds_for_active (r : Processing) :
    (∀ p ∈ (sendEntered fs st r).1.pending, p ∉ r.state.pending →
      ∃ e ∈ sendOrder r.state r.queue.entered, p.requester = .state e.1 e.2.1 ∧
        ∃ i, r.state.machine? e.1 = some i ∧ i.closed = false ∧ i.isIn e.2.1 = true) ∧
    ∀ c ∈ (sendEntered fs st r).1.machines, c ∉ r.state.machines →
      ∃ e ∈ sendOrder r.state r.queue.entered, c.opener.map (fun o => (o.parent, o.state)) = some (e.1, e.2.1) ∧
        ∃ i, r.state.machine? e.1 = some i ∧ i.closed = false ∧ i.isIn e.2.1 = true := by
  unfold sendEntered
  generalize sendOrder r.state r.queue.entered = es
  have key : ∀ (es : List (String × String × Nat)) (r : Processing),
      (∀ p ∈ (es.foldlM (m := Id) (fun r e => activateEntered fs st e r) r).1.pending, p ∉ r.state.pending →
        ∃ e ∈ es, p.requester = .state e.1 e.2.1 ∧
          ∃ i, r.state.machine? e.1 = some i ∧ i.closed = false ∧ i.isIn e.2.1 = true) ∧
      ∀ c ∈ (es.foldlM (m := Id) (fun r e => activateEntered fs st e r) r).1.machines, c ∉ r.state.machines →
        ∃ e ∈ es, c.opener.map (fun o => (o.parent, o.state)) = some (e.1, e.2.1) ∧
          ∃ i, r.state.machine? e.1 = some i ∧ i.closed = false ∧ i.isIn e.2.1 = true := by
    intro es
    induction es with
    | nil => intro r; exact ⟨fun p hp hn => absurd hp hn, fun c hc hn => absurd hc hn⟩
    | cons e es ih =>
      intro r
      simp only [List.foldlM_cons, id_bind]
      have hk := keepsEntered_activateEntered (fs := fs) (st := st) e r
      obtain ⟨ip, ic⟩ := ih (activateEntered fs st e r)
      obtain ⟨ap, ac⟩ := activateEntered_adds_for_active (fs := fs) (st := st) e r
      refine ⟨fun p hp hn => ?_, fun c hc hn => ?_⟩
      · by_cases hm : p ∈ (activateEntered fs st e r).1.pending
        · obtain ⟨h1, h3⟩ := ap p hm hn
          exact ⟨e, List.mem_cons_self, h1, h3⟩
        · obtain ⟨e', he', h1, i, hi, hc, hn'⟩ := ip p hp hm
          exact ⟨e', List.mem_cons_of_mem _ he', h1, hk.active hi hc hn'⟩
      · by_cases hm : c ∈ (activateEntered fs st e r).1.machines
        · obtain ⟨h1, h3⟩ := ac c hm hn
          exact ⟨e, List.mem_cons_self, h1, h3⟩
        · obtain ⟨e', he', h1, i, hi, hc', hn'⟩ := ic c hc hm
          exact ⟨e', List.mem_cons_of_mem _ he', h1, hk.active hi hc' hn'⟩
  exact key es _

end Tazuna.Thm.Service.Chart.Request
