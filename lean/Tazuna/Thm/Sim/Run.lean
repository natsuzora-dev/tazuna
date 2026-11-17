import Tazuna.Sim.Run
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Service.Queue

namespace Tazuna.Thm.Sim.Run

open Tazuna.Data Tazuna.Service Tazuna.Sim
open Tazuna.Thm.Data.Basic

variable {fsOf : String → Functions Id}

/-- `w'` is `w` with reports added after its own: no state, message, or halt differs. -/
def Reported (w w' : World) : Prop := ∃ rs, w' = { w with violations := w.violations ++ rs }

theorem reported_refl (w : World) : Reported w w := ⟨[], by simp⟩

theorem reported_trans {w₁ w₂ w₃ : World} (h₁ : Reported w₁ w₂) (h₂ : Reported w₂ w₃) : Reported w₁ w₃ := by
  obtain ⟨rs, rfl⟩ := h₁
  obtain ⟨qs, rfl⟩ := h₂
  exact ⟨rs ++ qs, by simp⟩

theorem reported_note {w w' : World} (h : Reported w w') (r : InvalidScenario) : Reported w (w'.note r) :=
  reported_trans h ⟨[r], rfl⟩

theorem reported_report {w w' : World} (h : Reported w w') (r : InvalidScenario) (hr : r.halts = false) :
    Reported w (w'.report r) := by
  unfold World.report
  simp only [hr, Bool.false_eq_true, ite_false]
  exact reported_note h r

theorem checkEnd_reported (w : World) : Reported w w.checkEnd := by
  unfold World.checkEnd
  refine foldl_keeps (Reported w) _ (fun w' x h => ?_) _ _ ?_
  · (repeat' split) <;> first | exact h | (apply reported_report h; rfl)
  · refine foldl_keeps (Reported w) _ (fun w' x h => ?_) _ _ ?_
    · (repeat' split) <;> first | exact h | (apply reported_report h; rfl)
    · refine foldl_keeps (Reported w) _ (fun w' x h => ?_) _ _ (reported_refl w)
      (repeat' split) <;> first | exact h | (apply reported_report h; rfl)

theorem expect_reported (w : World) (own : String) (lines : List Scenario.Line)
    (expectations : List Scenario.Expectation) (found : List (Nat × Except InvalidScenario Bool)) :
    Reported w (w.expect fsOf own lines expectations found) := by
  unfold World.expect
  rw [foldlM_id]
  refine foldl_keeps (Reported w) _ (fun w' x h => ?_) _ _ (reported_refl w)
  simp only [bind, pure]
  split
  · exact reported_note h _
  · split
    · exact reported_note h _
    · exact h
    · split
      · exact h
      · exact reported_note h _

theorem stepFinding_fst (sc : Scenario) (w : World) (found : List (Nat × Except InvalidScenario Bool)) (l : Scenario.Line)
    (i : Nat) : (World.stepFinding (m := Id) fsOf sc (w, found) l i).1 = w.step fsOf sc l i := by
  unfold World.stepFinding World.step
  by_cases h : w.stopped = true <;> simp [h, bind, pure]

theorem foldlM_stepFinding_fst (sc : Scenario) (xs : List (Scenario.Line × Nat)) (w : World)
    (found : List (Nat × Except InvalidScenario Bool)) :
    (xs.foldlM (m := Id) (fun wf (l, i) => World.stepFinding fsOf sc wf l i) (w, found)).1 =
      xs.foldlM (m := Id) (fun w (l, i) => w.step fsOf sc l i) w := by
  induction xs generalizing w found with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨l, i⟩ := x
    simp only [List.foldlM_cons, id_bind]
    rw [← stepFinding_fst sc w found l i]
    generalize World.stepFinding fsOf sc (w, found) l i = p
    obtain ⟨w', found'⟩ := p
    exact ih w' found'

/-- What `step` does with a scenario does not depend on its Then. -/
theorem step_then (w : World) (sc : Scenario) (then' : List Scenario.Expectation) (l : Scenario.Line) (i : Nat) :
    w.step fsOf { sc with expectations := then' } l i = w.step fsOf sc l i := rfl

/-- What Given does with a scenario does not depend on its Then. -/
theorem given_then (j : Spec.Structure) (w : World) (sc : Scenario) (then' : List Scenario.Expectation) :
    w.given j fsOf { sc with expectations := then' } = w.given j fsOf sc := rfl

/--
Then and the end checks only add violations: the world that `simulate` leaves is the one `execute` leaves, with the same
traces, messages, and halt, and more violations.
-/
theorem simulate_reported (j : Spec.Structure) (start : World) (sc : Scenario) :
    Reported (execute j fsOf start sc) (simulate j fsOf start sc) := by
  unfold simulate execute World.execute
  simp only [bind, pure]
  split
  · exact reported_refl _
  · rw [← foldlM_stepFinding_fst sc _ _ []]
    split
    · exact reported_refl _
    · exact reported_trans (checkEnd_reported _) (expect_reported _ _ _ _ _)

theorem expect_nil (w : World) (own : String) (lines : List Scenario.Line) (found : List (Nat × Except InvalidScenario Bool)) :
    w.expect fsOf own lines [] found = w := rfl

/--
Then only adds violations: the scenario leaves the same traces, messages, and halt as the scenario without its
expectations, so a snapshot depends on Given and When alone.
-/
theorem then_only_reports (j : Spec.Structure) (start : World) (sc : Scenario) :
    Reported (simulate j fsOf start { sc with expectations := [] }) (simulate j fsOf start sc) := by
  unfold simulate
  simp only [bind, pure, given_then]
  split
  · rename_i h
    simp only [h, ite_true]
    exact reported_refl _
  · rename_i h
    simp only [h, Bool.false_eq_true, ite_false]
    simp only [foldlM_stepFinding_fst, step_then]
    split
    · exact reported_refl _
    · rw [expect_nil]
      exact expect_reported _ _ _ _ _

/-- A report that halts stops the simulation. -/
theorem halting_report_stops (w : World) (r : InvalidScenario) (hr : r.halts = true) : (w.report r).stopped = true := by
  simp [World.report, World.stopped, hr]

theorem foldlM_step_stopped (sc : Scenario) (xs : List (Scenario.Line × Nat)) (w : World) (h : w.stopped = true) :
    xs.foldlM (m := Id) (fun w (l, i) => w.step fsOf sc l i) w = w := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldlM_cons, World.step, h, ite_true, id_bind, id_pure]; exact ih

/-- The lines after the one that stopped the simulation take no effect. -/
theorem lines_after_stop_ignored (sc : Scenario) (pre post : List (Scenario.Line × Nat)) (w : World)
    (h : (pre.foldlM (m := Id) (fun w (l, i) => w.step fsOf sc l i) w).stopped = true) :
    (pre ++ post).foldlM (m := Id) (fun w (l, i) => w.step fsOf sc l i) w =
      pre.foldlM (m := Id) (fun w (l, i) => w.step fsOf sc l i) w := by
  rw [List.foldlM_append, id_bind, foldlM_step_stopped sc post _ h]

/--
Every message in flight in `w`, except those at the places that `except` names, is in flight at the same place of `w'`
with the same content.
-/
def KeepsInFlight (except : Nat → Prop) (w w' : World) : Prop :=
  ∀ k msg, ¬except k → w.messages[k]? = some msg → msg.status = .inFlight → w'.messages[k]? = some msg

variable {e : Nat → Prop}

theorem keeps_refl (w : World) : KeepsInFlight e w w := fun _ _ _ h _ => h

theorem keeps_messages {w w' w'' : World} (h : KeepsInFlight e w w') (hm : w''.messages = w'.messages) :
    KeepsInFlight e w w'' := fun k msg hk hw hs => by rw [hm]; exact h k msg hk hw hs

theorem keeps_report {w w' : World} (h : KeepsInFlight e w w') (r : InvalidScenario) : KeepsInFlight e w (w'.report r) :=
  keeps_messages h (by unfold World.report; split <;> rfl)

theorem keeps_push {w w' : World} (h : KeepsInFlight e w w') (msg : Message) :
    KeepsInFlight e w { w' with messages := w'.messages.push msg } := fun k m hk hw hs => by
  have := h k m hk hw hs
  simp only [Array.getElem?_push]
  split
  · rename_i hk'
    subst hk'
    simp at this
  · exact this

theorem keeps_setStatus {w w' : World} (h : KeepsInFlight e w w') (k : Nat) (status : Status)
    (hk : e k ∨ ∀ msg, w'.messages[k]? = some msg → msg.status ≠ .inFlight) :
    KeepsInFlight e w (w'.setStatus k status) := fun j m hj hw hs => by
  have hj' := h j m hj hw hs
  unfold World.setStatus
  simp only [Array.getElem?_modify]
  split
  · rename_i hjk
    subst hjk
    rcases hk with hk | hk
    · exact absurd hk hj
    · exact absurd hs (hk m hj')
  · exact hj'

theorem keeps_post {w w' : World} (h : KeepsInFlight e w w') (o : Scenario.Origin) (sender receiver : String) (l : Line)
    (channel : Option String) : KeepsInFlight e w (w'.post o sender receiver l channel) := by
  unfold World.post
  dsimp only
  split
  · exact keeps_report h _
  · exact keeps_push h _

theorem keeps_route {w w' : World} (h : KeepsInFlight e w w') (o : Scenario.Origin) (service : String)
    (lines : List Line) : KeepsInFlight e w (w'.route o service lines) := by
  unfold World.route
  refine foldl_keeps (KeepsInFlight e w) _ (fun v l hv => ?_) _ _ h
  dsimp only
  (repeat' split) <;> first
    | exact hv
    | exact keeps_post hv _ _ _ _ _
    | (refine foldl_keeps (KeepsInFlight e w) _ (fun u x hu => ?_) _ _ hv
       split <;> first | exact hu | exact keeps_post hu _ _ _ _ _)

theorem keeps_checkComputed {w w' : World} (h : KeepsInFlight e w w') (service : String) (sent : List Line)
    (records : Records) : KeepsInFlight e w (w'.checkComputed service sent records) := by
  unfold World.checkComputed
  repeat' split
  all_goals exact keeps_messages h rfl

theorem keeps_act {w w' : World} (h : KeepsInFlight e w w') (o : Scenario.Origin) (service : String)
    (f : Service → Functions Id → State → Id State) (reopen : Bool) :
    KeepsInFlight e w (w'.act fsOf o service f reopen) := by
  unfold World.act
  split
  · exact h
  · apply keeps_checkComputed
    apply keeps_route
    exact keeps_messages h rfl

theorem keeps_deliver {w w' : World} (h : KeepsInFlight e w w') (o : Scenario.Origin) (k : Nat)
    (hk : e k ∨ ∀ msg, w'.messages[k]? = some msg → msg.status ≠ .inFlight) :
    KeepsInFlight e w (w'.deliver fsOf o k) := by
  unfold World.deliver
  split
  · exact h
  · exact keeps_act (keeps_setStatus h k _ hk) _ _ _ _

theorem keeps_carry {w w' : World} (h : KeepsInFlight e w w') (i k : Nat) : KeepsInFlight e w (w'.carry i k) :=
  keeps_messages h rfl

theorem keeps_recordSent {w w' : World} (h : KeepsInFlight e w w') (i : Nat) (service : String) (before : Nat) :
    KeepsInFlight e w (w'.recordSent i service before) :=
  keeps_messages h (by unfold World.recordSent; split <;> rfl)

theorem keeps_stated {w w' : World} (h : KeepsInFlight e w w') (i : Nat) (msg : Message) :
    KeepsInFlight e w (w'.stated i msg) := by
  unfold World.stated
  split
  · exact keeps_report h _
  · exact keeps_carry (keeps_push h _) _ _

theorem keeps_resolving {α : Type} {w w' : World} (h : KeepsInFlight e w w') (r : ExceptT InvalidScenario Id α)
    (k : α → Id World) (hk : ∀ a, KeepsInFlight e w (k a)) : KeepsInFlight e w (w'.resolving r k) := by
  unfold World.resolving
  simp only [bind]
  split
  · exact keeps_report h _
  · exact hk _

theorem keeps_attempt {α : Type} {w w' : World} (h : KeepsInFlight e w w') (r : Except InvalidScenario α)
    (k : α → Id World) (hk : ∀ a, KeepsInFlight e w (k a)) : KeepsInFlight e w (w'.attempt r k) := by
  unfold World.attempt
  split
  · exact keeps_report h _
  · exact hk _

theorem keeps_nextId {w w' : World} (h : KeepsInFlight e w w') (peer name : String) :
    KeepsInFlight e w (w'.nextId peer name).1 :=
  keeps_messages h rfl

theorem keeps_now_iff {w w' : World} (now : Time) : KeepsInFlight e w { w' with now } ↔ KeepsInFlight e w w' :=
  Iff.rfl

theorem keeps_inFlight_iff {w w' : World} (leftInFlight : List (Nat × Nat)) :
    KeepsInFlight e w { w' with leftInFlight } ↔ KeepsInFlight e w w' := Iff.rfl

/-- Closes `KeepsInFlight e w x` where `x` is built from `w` by the steps that keep in-flight messages. -/
macro "keeps_tac" : tactic => `(tactic| repeat' (first
  | contradiction
  | with_reducible assumption
  | with_reducible exact keeps_refl _
  | with_reducible apply keeps_report
  | with_reducible apply keeps_carry
  | with_reducible apply keeps_recordSent
  | with_reducible apply keeps_stated
  | with_reducible apply keeps_nextId
  | with_reducible apply keeps_act
  | with_reducible apply keeps_push
  | simp only [keeps_now_iff, keeps_inFlight_iff]
  | with_reducible refine keeps_resolving ?_ _ _ fun _ => ?_
  | with_reducible refine keeps_attempt ?_ _ _ fun _ => ?_
  | with_reducible refine foldl_keeps _ _ (fun _ _ _ => ?_) _ _ ?_
  | dsimp only
  | split))

theorem keeps_deliverCarried {w w' : World} (h : KeepsInFlight e w w') (i k : Nat)
    (hk : e k ∨ ∀ msg, w'.messages[k]? = some msg → msg.status ≠ .inFlight) :
    KeepsInFlight e w (w'.deliverCarried fsOf i k) := by
  unfold World.deliverCarried
  simp only [bind, pure]
  keeps_tac
  all_goals first | exact keeps_setStatus (keeps_carry h _ _) _ _ hk | exact keeps_deliver (keeps_carry h _ _) _ _ hk

theorem keeps_clientRequest {w w' : World} (h : KeepsInFlight e w w') (i : Nat) (type : Scenario.RequestType)
    (target : Spec.Ref) (input : Scenario.Template) (sameIdAs : Option Nat) :
    KeepsInFlight e w (w'.clientRequest fsOf i type target input sameIdAs) := by
  unfold World.clientRequest
  simp only [bind, pure]
  keeps_tac

theorem status_ne {w : World} {k : Nat} {msg : Message} {s : Status} (hm : w.messages[k]? = some msg)
    (hs : ¬(msg.status != s) = true) (hne : s ≠ .inFlight) :
    ∀ m, w.messages[k]? = some m → m.status ≠ .inFlight := by
  intro m hm' hst
  rw [hm] at hm'
  cases hm'
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hs
  exact hne (hs ▸ hst)

/-- What the line moves: the message that a deliver, lose, or refuse line names. -/
def moved : Scenario.Line → Option Scenario.Fact
  | .deliver f | .lose f | .refuse f => some f
  | _ => none

theorem take_keeps (w : World) (own : String) (lines : List Scenario.Line) (i : Nat)
    (l : Scenario.Line) (hl : moved l = none) :
    KeepsInFlight (fun _ => False) w (w.take fsOf own lines i l) := by
  cases l <;> simp only [moved, reduceCtorEq] at hl <;> simp only [World.take, bind, pure, foldlM_id]
  all_goals keeps_tac
  all_goals first
    | exact keeps_clientRequest (keeps_refl _) _ _ _ _ _
    | (apply keeps_setStatus (keeps_refl _); right; apply status_ne (s := .delivered) <;> first | assumption | decide)
    | (apply keeps_deliverCarried (keeps_refl _); right; apply status_ne (s := .delivered) <;> first | assumption | decide)

theorem keeps_absent {w w' : World} {n : Nat} (h : KeepsInFlight (fun j => e j ∨ j = n) w w')
    (hn : w.messages[n]? = none) : KeepsInFlight e w w' := fun k msg hk hm hs =>
  h k msg (fun hk' => hk'.elim hk fun hkn => by rw [hkn, hn] at hm; cases hm) hm hs

theorem checkWritten_halts {w : World} {i : Nat} {written picks : List Scenario.Template} {allowed : Bool}
    {r : InvalidScenario} (h : w.checkWritten i written picks allowed = some r) : r.halts = true := by
  unfold World.checkWritten at h
  split at h
  · cases h; rfl
  · obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp h
    cases h; rfl

theorem line_eq (w : World) (own : String) (lines : List Scenario.Line) (i : Nat)
    (l : Scenario.Line) :
    w.line fsOf own lines i l = w.take fsOf own lines i l ∨
      ∃ r, r.halts = true ∧ w.line fsOf own lines i l = w.report r := by
  unfold World.line
  dsimp only
  (repeat' split) <;> first | exact Or.inl rfl | exact Or.inr ⟨_, checkWritten_halts ‹_›, rfl⟩

/--
A line that is not a deliver, lose, or refuse line leaves every message in flight as it is: no message reaches its
receiver, or is lost, unless a line names it.
-/
theorem line_keeps_leftInFlight (w : World) (own : String) (lines : List Scenario.Line)
    (i : Nat) (l : Scenario.Line) (hl : moved l = none) :
    KeepsInFlight (fun _ => False) w (w.line fsOf own lines i l) := by
  rcases line_eq w own lines i l with h | ⟨r, -, h⟩ <;> rw [h]
  · exact take_keeps w own lines i l hl
  · exact keeps_report (keeps_refl w) r

/--
A deliver, lose, or refuse line leaves every message in flight as it is, except the one its handle names.
-/
theorem moving_line_keeps_others (w : World) (own : String) (lines : List Scenario.Line)
    (i : Nat) (l : Scenario.Line) (f : Scenario.Fact) (hl : moved l = some f) (k : Nat)
    (hk : (w.messageOf fsOf i f).run = .ok k) :
    KeepsInFlight (· = k) w (w.line fsOf own lines i l) := by
  rcases line_eq w own lines i l with h | ⟨r, -, h⟩ <;> rw [h]
  · cases l <;> simp only [moved, reduceCtorEq, Option.some.injEq] at hl <;> subst hl <;>
      simp only [World.take, World.resolving, bind, pure, hk]
    all_goals try (unfold World.deliverInOrder; simp only [pure])
    all_goals (repeat' split) <;> first
      | with_reducible exact keeps_refl w
      | with_reducible exact keeps_report (keeps_refl w) _
      | with_reducible exact keeps_deliverCarried (keeps_refl w) _ _ (Or.inl rfl)
      | with_reducible exact keeps_setStatus (keeps_refl w) _ _ (Or.inl rfl)
      | (refine keeps_absent (n := w.messages.size) ?_ (by simp)
         refine keeps_deliverCarried (e := fun j => j = k ∨ j = w.messages.size) (keeps_push (keeps_setStatus (keeps_refl w) _ _ (Or.inl (Or.inl rfl))) _)
           _ _ (Or.inl (Or.inr ?_))
         simp [World.setStatus])
  · exact keeps_report (keeps_refl w) r

/--
A deliver line whose message has an earlier message in flight on its channel delivers nothing and stops the
simulation with a violation: messages on one channel reach their receiver in sending order.
-/
theorem overtaking_delivery_halts (w : World) (own : String) (lines : List Scenario.Line)
    (i : Nat) (f : Scenario.Fact) (k : Nat) (msg : Message)
    (hk : (w.messageOf fsOf i f).run = .ok k) (hm : w.messages[k]? = some msg) (j : Nat) (n : Message) (hj : j < k)
    (hn : w.messages[j]? = some n) (hs : n.status = .inFlight) (hc : n.sameChannel msg = true) :
    ∃ r, r.halts = true ∧ w.line fsOf own lines i (.deliver f) = w.report r := by
  rcases line_eq w own lines i (.deliver f) with h | h
  · rw [h]
    simp only [World.take, World.resolving, bind, pure, hk, hm]
    split
    · exact ⟨_, rfl, rfl⟩
    · unfold World.deliverInOrder
      simp only [hm]
      have hmem : n ∈ w.messages.toList.take k := by
        apply List.mem_of_getElem? (i := j)
        simp [hj, hn]
      have hfind : ((w.messages.toList.take k).find? fun x => x.status == .inFlight && x.sameChannel msg).isSome :=
        List.find?_isSome.mpr ⟨n, hmem, by simp [hs, hc]⟩
      obtain ⟨earlier, he⟩ := Option.isSome_iff_exists.mp hfind
      rw [he]
      exact ⟨_, rfl, rfl⟩
  · exact h

/--
An external peer's answer line names a request that reached that peer: otherwise it sends nothing and stops the
simulation with a report.
-/
theorem external_answer_needs_delivery (w : World) (own : String) (lines : List Scenario.Line)
    (i : Nat) (peer : String) (f : Scenario.Fact) (a : Scenario.Template) (k : Nat)
    (msg : Message) (hr : w.role peer = some .external) (hk : (w.messageOf fsOf i f).run = .ok k)
    (hm : w.messages[k]? = some msg) (hd : ¬(msg.receiver = peer ∧ msg.status = .delivered)) :
    ∃ r, r.halts = true ∧ w.line fsOf own lines i (.answer peer f a) = w.report r := by
  rcases line_eq w own lines i (.answer peer f a) with h | h
  · rw [h]
    simp only [World.take, World.resolving, bind, pure, hk, hm, hr]
    split
    · exact ⟨_, rfl, rfl⟩
    · split
      · exact ⟨_, rfl, rfl⟩
      · rename_i hne hst
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne hst
        exact absurd ⟨hne, hst⟩ hd
  · exact h

/-- `w'` holds every running service's state as `w` holds it. -/
def SameStates (w w' : World) : Prop := w'.states = w.states

theorem same_refl (w : World) : SameStates w w := rfl

theorem same_report {w w' : World} (h : SameStates w w') (r : InvalidScenario) : SameStates w (w'.report r) := by
  unfold SameStates World.report; split <;> exact h

theorem same_carry {w w' : World} (h : SameStates w w') (i k : Nat) : SameStates w (w'.carry i k) := h

theorem same_setStatus {w w' : World} (h : SameStates w w') (k : Nat) (status : Status) :
    SameStates w (w'.setStatus k status) := h

theorem same_stated {w w' : World} (h : SameStates w w') (i : Nat) (msg : Message) : SameStates w (w'.stated i msg) := by
  unfold World.stated; split
  · exact same_report h _
  · exact h

theorem same_nextId {w w' : World} (h : SameStates w w') (peer name : String) : SameStates w (w'.nextId peer name).1 := h

theorem same_inFlight_iff {w w' : World} (leftInFlight : List (Nat × Nat)) :
    SameStates w { w' with leftInFlight } ↔ SameStates w w' := Iff.rfl

theorem same_resolving {α : Type} {w w' : World} (h : SameStates w w') (r : ExceptT InvalidScenario Id α)
    (k : α → Id World) (hk : ∀ a, SameStates w (k a)) : SameStates w (w'.resolving r k) := by
  unfold World.resolving; simp only [bind]; split
  · exact same_report h _
  · exact hk _

theorem same_attempt {α : Type} {w w' : World} (h : SameStates w w') (r : Except InvalidScenario α)
    (k : α → Id World) (hk : ∀ a, SameStates w (k a)) : SameStates w (w'.attempt r k) := by
  unfold World.attempt; split
  · exact same_report h _
  · exact hk _

/-- Closes `SameStates w x` where `x` is built from `w` by steps that change no running service's state. -/
macro "same_tac" : tactic => `(tactic| repeat' (first
  | contradiction
  | with_reducible assumption
  | with_reducible exact same_refl _
  | with_reducible apply same_report
  | with_reducible apply same_carry
  | with_reducible apply same_stated
  | with_reducible apply same_nextId
  | with_reducible apply same_setStatus
  | simp only [same_inFlight_iff]
  | with_reducible refine same_resolving ?_ _ _ fun _ => ?_
  | with_reducible refine same_attempt ?_ _ _ fun _ => ?_
  | with_reducible refine foldl_keeps _ _ (fun _ _ _ => ?_) _ _ ?_
  | dsimp only
  | split))

/--
Whether the line gives a running service something to process: a request or end of the client, a resend, an operation, the
clock, a restart, or a message that a deliver, redeliver, or refuse line names.
-/
def reaches : Scenario.Line → Bool
  | .request none .. | .unsubscribe none _ | .resend _ | .operate .. | .at .. | .restart
  | .deliver _ | .redeliver _ | .refuse _ => true
  | _ => false

/--
A line that gives no running service anything to process changes no running service's state: a peer's message, an answer, an
event, a lost message, or a leaveInFlight or look line leaves every receiver as it was until a line delivers the message.
-/
theorem line_keeps_states (w : World) (own : String) (lines : List Scenario.Line) (i : Nat) (l : Scenario.Line)
    (hl : reaches l = false) : (w.line fsOf own lines i l).states = w.states := by
  rcases line_eq w own lines i l with h | ⟨r, -, h⟩ <;> rw [h]
  · show SameStates w _
    cases l with
    | request peer =>
      cases peer with
      | none => simp [reaches] at hl
      | some p => simp only [World.take, bind, pure]; same_tac
    | unsubscribe peer =>
      cases peer with
      | none => simp [reaches] at hl
      | some p => simp only [World.take, bind, pure]; same_tac
    | _ => simp only [reaches, reduceCtorEq] at hl <;> simp only [World.take, bind, pure] <;> same_tac
  · exact same_report (same_refl w) r

/-- A clock line sends each subscription answer that the new time changes, after its time line. -/
theorem clock_line_publishes (time : Time) (st : Service) (fs : Functions Id) (s : State)
    (h : (fireDue st fs time Limit.dueDeadlines.max none s).halted = none) :
    fireTo time st fs s =
      let t := fireDue st fs time Limit.dueDeadlines.max none s
      publish st fs ({ t with now := max t.now time }.write .in none .time).1 := by
  simp [fireTo, h]

/-- An answer that arrives again with the id of an earlier one is written and not processed again. -/
theorem redelivered_answer_not_processed (st : Service) (fs : Functions Id) (s : State) (id to : String) (a : Answer)
    (hd : id ∈ s.deliveries) :
    answerIn st fs s id to a = message st fs (s.write .in (some id) (.answer to a)).1.newMessage {} := by
  simp [answerIn, hd]

/--
An answer to a request of the service is kept for a later result event, also when the request waits no more, as after
a restart.
-/
theorem late_answer_taken (st : Service) (fs : Functions Id) (s : State) (id to : String) (a : Answer)
    (target : Spec.Ref) (hd : id ∉ s.deliveries) (ht : requestTarget? st s to = some target)
    (hp : s.pending.find? (·.id == to) = none) :
    (answerIn st fs s id to a).takenAnswers.lookup to = some (target, a) := by
  simp [answerIn, hd, ht, hp, Tazuna.Thm.Service.Queue.message_takenAnswers, State.write, State.newMessage]

end Tazuna.Thm.Sim.Run
