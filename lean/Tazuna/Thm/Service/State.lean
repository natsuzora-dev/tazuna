import Tazuna.Service.State
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Service.Chart.Basic
import Tazuna.Thm.Service.Functions

namespace Tazuna.Thm.Service.State

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic Tazuna.Thm.Service.Functions

variable {st : Service} {fs : Functions Id} {s : State}

@[simp] theorem fault_halts (f : Fault) : (Finding.fault f).halts = f.halts := rfl

/-- The parts of a state that internal queue work never changes. -/
structure Fixed where
  commandAnswers : CommandAnswers
  records : Records
  now : Time
  started : Bool
  service : String

def _root_.Tazuna.Service.State.fixed (s : State) : Fixed :=
  ⟨s.commandAnswers, s.records, s.now, s.started, s.service⟩

@[simp] theorem write_fixed (d : Dir) (g : Option LineId) (b : LineBody) (w : EmittedOf d b)
    (q : SenderOf d b) (r : RequestOf d b) : (s.write d g b w q r).1.fixed = s.fixed := rfl

@[simp] theorem await_fixed (b : LineBody) (q : Requester) (a : Activity) (i : Value) :
    (s.await b q a i).fixed = s.fixed := by
  simp [State.await, State.fixed, State.write]

@[simp] theorem write_commandAnswers (d : Dir) (g : Option LineId) (b : LineBody) (w : EmittedOf d b) (q : SenderOf d b) (r : RequestOf d b) :
    (s.write d g b w q r).1.commandAnswers = s.commandAnswers := rfl

@[simp] theorem newStep_commandAnswers (o : StepOrigin) : (s.newStep o).1.commandAnswers = s.commandAnswers := rfl

@[simp] theorem newMessage_commandAnswers :
    s.newMessage.commandAnswers = s.commandAnswers := rfl

@[simp] theorem halt_commandAnswers (v : Finding) : (s.halt v).commandAnswers = s.commandAnswers := rfl

@[simp] theorem violate_commandAnswers (v : Finding) : (s.violate v).commandAnswers = s.commandAnswers := rfl

@[simp] theorem report_fixed (f : Finding) : (s.report f).fixed = s.fixed := by
  unfold State.report; split <;> rfl

@[simp] theorem report_commandAnswers (f : Finding) :
    (s.report f).commandAnswers = s.commandAnswers := by
  unfold State.report; split <;> rfl

@[simp] theorem report_started (f : Finding) : (s.report f).started = s.started := by
  unfold State.report; split <;> rfl

@[simp] theorem report_records (f : Finding) : (s.report f).records = s.records := by
  unfold State.report; split <;> rfl

@[simp] theorem report_lines (f : Finding) : (s.report f).lines = s.lines := by
  unfold State.report; split <;> rfl

@[simp] theorem report_now (f : Finding) : (s.report f).now = s.now := by
  unfold State.report; split <;> rfl

@[simp] theorem report_service (f : Finding) : (s.report f).service = s.service := by
  unfold State.report; split <;> rfl

theorem report_eq (f : Finding) :
    s.report f = { s with halted := if f.halts then some f else s.halted,
                          violations := if f.halts then s.violations else s.violations ++ [f] } := by
  unfold State.report State.halt State.violate
  split <;> rfl

@[simp] theorem report_machines (f : Finding) : (s.report f).machines = s.machines := by
  simp [report_eq]

@[simp] theorem report_copies (f : Finding) : (s.report f).copies = s.copies := by
  simp [report_eq]

@[simp] theorem report_pending (f : Finding) : (s.report f).pending = s.pending := by
  simp [report_eq]

@[simp] theorem report_deadlines (f : Finding) : (s.report f).deadlines = s.deadlines := by
  simp [report_eq]

@[simp] theorem report_stack (f : Finding) : (s.report f).stack = s.stack := by
  simp [report_eq]

theorem report_halted (f : Finding) (h : f.halts = true) : (s.report f).halted = some f := by
  simp [State.report, h, State.halt]

theorem reportAll_cons (t : State) (f : Fault) (fs : List Fault) :
    t.reportAll (f :: fs) = (if t.halted.isSome then t else t.report (.fault f)).reportAll fs := rfl

theorem reportAll_preserves {α : Type} (g : State → α) (hg : ∀ (t : State) f, g (t.report (.fault f)) = g t)
    (fs : List Fault) (t : State) : g (t.reportAll fs) = g t := by
  induction fs generalizing t with
  | nil => rfl
  | cons f fs ih =>
    rw [reportAll_cons, ih]
    split <;> simp [hg]

@[simp] theorem reportAll_fixed (fs : List Fault) : (s.reportAll fs).fixed = s.fixed :=
  reportAll_preserves State.fixed (fun _ _ => report_fixed ..) fs s

@[simp] theorem reportAll_commandAnswers (fs : List Fault) :
    (s.reportAll fs).commandAnswers = s.commandAnswers :=
  reportAll_preserves (·.commandAnswers) (fun _ _ => report_commandAnswers ..) fs s

@[simp] theorem reportAll_started (fs : List Fault) : (s.reportAll fs).started = s.started :=
  reportAll_preserves (·.started) (fun _ _ => report_started ..) fs s

@[simp] theorem reportAll_records (fs : List Fault) : (s.reportAll fs).records = s.records :=
  reportAll_preserves (·.records) (fun _ _ => report_records ..) fs s

@[simp] theorem reportAll_lines (fs : List Fault) : (s.reportAll fs).lines = s.lines :=
  reportAll_preserves State.lines (fun _ _ => report_lines ..) fs s

@[simp] theorem reportAll_subscriptions (fs : List Fault) :
    (s.reportAll fs).subscriptions = s.subscriptions :=
  reportAll_preserves (·.subscriptions) (fun _ _ => by unfold State.report; split <;> rfl) fs s

@[simp] theorem reportAll_now (fs : List Fault) : (s.reportAll fs).now = s.now :=
  reportAll_preserves State.now (fun _ _ => report_now ..) fs s

@[simp] theorem reportAll_service (fs : List Fault) : (s.reportAll fs).service = s.service :=
  reportAll_preserves (·.service) (fun _ _ => report_service ..) fs s

@[simp] theorem setMachine_commandAnswers (name : InstanceId) (f : Instance → Instance) :
    (s.setMachine name f).commandAnswers = s.commandAnswers := rfl

@[simp] theorem answer_commandAnswers (to : Option LineId) (d : Spec.Ref) (a : Answer) :
    (s.answer to d a).commandAnswers = s.commandAnswers := by
  cases to <;> rfl

theorem copy_ne (i : InstanceId) (map : String) (key : Value) : InstanceId.copy i map key ≠ i := by
  intro h
  have := congrArg sizeOf h
  simp only [InstanceId.copy.sizeOf_spec] at this
  omega

theorem documentOrder_owner (i : Instance) :
    i.documentOrder.filter (·.1 == i.id) = i.chart.states.map fun cs => (i.id, cs.spec.name) := by
  unfold Instance.documentOrder
  generalize i.chart.states = l
  induction l with
  | nil => rfl
  | cons cs rest ih =>
    rw [List.flatMap_cons, List.filter_append, ih, List.filter_cons]
    have hb : ((i.copyKeysOf cs.spec.name).flatMap fun k => (i.chart.tree.descendants cs.spec.name).map (InstanceId.copy i.id cs.spec.name k, ·)).filter
        (·.1 == i.id) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      obtain ⟨k, -, ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨d, -, rfl⟩ := List.mem_map.mp ha
      simpa using copy_ne i.id cs.spec.name k
    simp [hb]

theorem emitAll_fixed (r : Option LineId) (es : List (Emit × EmittedBy)) : (s.emitAll r es).fixed = s.fixed := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => exact ih (s := (s.write .out none (.event e.1.event e.1.payload r) e.2).1)

theorem foldl_fixed {α : Type} (f : State → α → State) (h : ∀ t x, (f t x).fixed = t.fixed) (xs : List α)
    (t : State) : (xs.foldl f t).fixed = t.fixed := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih, h]

/-- The parts of a state that a message never changes. -/
def _root_.Tazuna.Service.State.clock (s : State) : CommandAnswers × Time := (s.commandAnswers, s.now)

theorem emitAll_clock (t : State) (r : Option LineId) (es : List (Emit × EmittedBy)) : (t.emitAll r es).clock = t.clock := by
  have h := emitAll_fixed (s := t) r es
  exact Prod.ext (congrArg Fixed.commandAnswers h) (congrArg Fixed.now h)

/--
Each `out` line of `lines` has the id that State.write gives a line without one under `service`: its name and one more
than the count of the lines before it with that name.
-/
def Numbered (service : String) (lines : Array Line) : Prop :=
  ∀ pre l, pre ++ [l] <+: lines.toList → l.dir = .out →
    l.id = .own s!"{l.body.idName service}#{namedCount service pre.toArray (l.body.idName service) + 1}"

theorem numbered_empty (service : String) : Numbered service #[] := fun pre l h _ => by
  have := h.length_le
  simp at this

theorem numbered_push {service : String} {lines : Array Line} {l : Line} :
    Numbered service (lines.push l) ↔ Numbered service lines ∧
      (l.dir = .out →
        l.id = .own s!"{l.body.idName service}#{namedCount service lines (l.body.idName service) + 1}") := by
  refine ⟨fun h => ⟨fun pre x hp => h pre x (hp.trans (by simp)), h _ _ (by simp)⟩, fun ⟨h, hl⟩ pre x hp => ?_⟩
  rcases List.prefix_concat_iff.mp (by simpa using hp) with he | hp
  · obtain ⟨rfl, hx⟩ := List.append_inj' he rfl
    cases hx
    simpa using hl
  · exact h pre x hp

/-- `s'` keeps the lines of `s`, adding lines at the time of `s`, and numbers its `out` lines as State.write does. -/
def Grows (s s' : State) : Prop :=
  (∃ new, s'.lines = s.lines ++ new ∧ ∀ l ∈ new, l.time = s.now) ∧
    (Numbered s.service s.lines → Numbered s'.service s'.lines)

theorem Grows.refl (s : State) : Grows s s := ⟨⟨#[], by simp, by simp⟩, id⟩

theorem Grows.of_lines {s s' : State} (h : s'.lines = s.lines) (hs : s'.service = s.service := by first | rfl | simp) :
    Grows s s' :=
  ⟨⟨#[], by simp [h], by simp⟩, by rw [h, hs]; exact id⟩

theorem Grows.trans {a b c : State} (h₁ : Grows a b) (hn : b.now = a.now) (h₂ : Grows b c) : Grows a c := by
  obtain ⟨⟨n₁, e₁, t₁⟩, m₁⟩ := h₁
  obtain ⟨⟨n₂, e₂, t₂⟩, m₂⟩ := h₂
  refine ⟨⟨n₁ ++ n₂, by rw [e₂, e₁, Array.append_assoc], ?_⟩, m₂ ∘ m₁⟩
  intro l hl
  rcases Array.mem_append.mp hl with h | h
  · exact t₁ l h
  · rw [t₂ l h, hn]

theorem Grows.bridge {a b c : State} (h : Grows b c) (hl : b.lines = a.lines) (hn : b.now = a.now)
    (hs : b.service = a.service := by first | rfl | simp) : Grows a c :=
  (Grows.of_lines hl hs).trans hn h

theorem grows_write (d : Dir) (g : Option LineId) (b : LineBody) (w : EmittedOf d b := by exact ())
    (q : SenderOf d b) (r : RequestOf d b) (hg : d = .out → g = none := by simp) : Grows s (s.write d g b w q r).1 :=
  ⟨⟨#[_], Array.push_eq_append, by simp⟩, fun h => numbered_push.mpr ⟨h, fun hd => by
    simp [State.write, State.lineId, hg hd]⟩⟩

@[simp] theorem takeQueued_service (n : Nat) : (s.takeQueued n).1.service = s.service := rfl

@[simp] theorem newCommandStep_service (c : Nat) (sender : Spec.Ref) :
    (s.newCommandStep c sender).1.1.service = s.service := rfl

@[simp] theorem await_service (b : LineBody) (q : Requester) (a : Activity) (i : Value) :
    (s.await b q a i).service = s.service := rfl

@[simp] theorem createKeys_service (es : List String) : (s.createKeys es).service = s.service := rfl

theorem await_grows (b : LineBody) (q : Requester) (a : Activity) (i : Value) : Grows s (s.await b q a i) :=
  (grows_write (s := s) .out none b default _ _).trans rfl (Grows.of_lines rfl)

theorem foldl_grows {α : Type} (f : State → α → State) (h : ∀ t x, Grows t (f t x)) (hn : ∀ t x, (f t x).now = t.now)
    (xs : List α) (t : State) : Grows t (xs.foldl f t) := by
  induction xs generalizing t with
  | nil => exact Grows.refl _
  | cons x xs ih => simp only [List.foldl_cons]; exact (h t x).trans (hn t x) (ih _)

theorem emitAll_grows (t : State) (r : Option LineId) (es : List (Emit × EmittedBy)) : Grows t (t.emitAll r es) := by
  unfold State.emitAll
  induction es generalizing t with
  | nil => exact Grows.refl _
  | cons e es ih => exact (grows_write _ _ _ _ _ _).trans rfl (ih _)

theorem answer_grows (t : State) (to : Option LineId) (d : Spec.Ref) (a : Answer) : Grows t (t.answer to d a) := by
  cases to
  · exact Grows.refl _
  · exact grows_write _ _ _ _ _ _

theorem answer_records (t : State) (to : Option LineId) (d : Spec.Ref) (a : Answer) : (t.answer to d a).records = t.records := by
  cases to <;> rfl

@[simp] theorem write_records (d : Dir) (g : Option LineId) (b : LineBody) (w : EmittedOf d b) (q : SenderOf d b) (r : RequestOf d b) :
    (s.write d g b w q r).1.records = s.records := rfl

@[simp] theorem write_deliveries (d : Dir) (g : Option LineId) (b : LineBody) (w : EmittedOf d b) (q : SenderOf d b) (r : RequestOf d b) :
    (s.write d g b w q r).1.deliveries = s.deliveries := rfl

@[simp] theorem write_halted (d : Dir) (g : Option LineId) (b : LineBody) (w : EmittedOf d b) (q : SenderOf d b) (r : RequestOf d b) :
    (s.write d g b w q r).1.halted = s.halted := rfl

@[simp] theorem write_id (d : Dir) (id : LineId) (b : LineBody) (w : EmittedOf d b) (q : SenderOf d b) (r : RequestOf d b) :
    (s.write d (some id) b w q r).2 = id := rfl

@[simp] theorem write_now (d : Dir) (g : Option LineId) (b : LineBody) (w : EmittedOf d b) (q : SenderOf d b) (r : RequestOf d b) :
    (s.write d g b w q r).1.now = s.now := rfl

@[simp] theorem newStep_now (o : StepOrigin) : (s.newStep o).1.now = s.now := rfl

@[simp] theorem newMessage_now : s.newMessage.now = s.now := rfl

@[simp] theorem answer_now (to : Option LineId) (d : Spec.Ref) (a : Answer) : (s.answer to d a).now = s.now := by
  cases to <;> rfl

@[simp] theorem newStep_records (o : StepOrigin) : (s.newStep o).1.records = s.records := rfl

@[simp] theorem newMessage_records : s.newMessage.records = s.records := rfl

@[simp] theorem newStep_deliveries (o : StepOrigin) :
    (s.newStep o).1.deliveries = s.deliveries := rfl

@[simp] theorem newStep_halted (o : StepOrigin) : (s.newStep o).1.halted = s.halted := rfl

@[simp] theorem newMessage_halted : s.newMessage.halted = s.halted := rfl

@[simp] theorem answer_halted (to : Option LineId) (d : Spec.Ref) (a : Answer) : (s.answer to d a).halted = s.halted := by
  cases to <;> rfl

/-- The state and the step after `send` writes the input line and begins the message and its step. -/
def sent (s : State) (name : Spec.Ref) (id : LineId) (input : Value) (caller : Caller) : State × Nat :=
  (s.write .in (some id) (.command name input caller)).1.newMessage.newStep .root

/-- The state after `receive` writes the input line. -/
def AddsOnly (P : Line → Prop) (s s' : State) : Prop := ∃ new, s'.lines = s.lines ++ new ∧ ∀ l ∈ new, P l

theorem AddsOnly.trans {P : Line → Prop} {a b c : State} (h₁ : AddsOnly P a b) (h₂ : AddsOnly P b c) :
    AddsOnly P a c := by
  obtain ⟨n₁, e₁, p₁⟩ := h₁
  obtain ⟨n₂, e₂, p₂⟩ := h₂
  refine ⟨n₁ ++ n₂, by rw [e₂, e₁, Array.append_assoc], fun l hl => ?_⟩
  rcases Array.mem_append.mp hl with h | h
  · exact p₁ l h
  · exact p₂ l h

def CopiesOf (chart : Chart) (map : String) (cs : List Instance) : Prop :=
  ∀ c ∈ cs, c.chart = chart ∧ c.id.map? = some map

end Tazuna.Thm.Service.State
