import Tazuna.Sim.Run
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Service.Queue
import Tazuna.Thm.Guarantee

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
Then and the end checks only add violations: the world that `simulate` leaves is the one `execute` leaves after the run
ends, with the same traces, messages, and halt, and more violations.
-/
@[guarantee] theorem simulate_reported (j : Spec.Structure) (start : World) (sc : Scenario)
    (h : (start.given j fsOf sc).violations = []) :
    Reported ((execute j fsOf start sc).ended fsOf) (simulate j fsOf start sc) := by
  unfold simulate execute World.execute
  simp only [bind, pure, h, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [← foldlM_stepFinding_fst sc _ _ []]
  split
  · exact reported_refl _
  · exact reported_trans (checkEnd_reported _) (expect_reported _ _ _ _ _)

theorem expect_nil (w : World) (own : String) (lines : List Scenario.Line) (found : List (Nat × Except InvalidScenario Bool)) :
    w.expect fsOf own lines [] found = w := rfl

/--
Then only adds violations: the scenario leaves the same traces, messages, and halt as the scenario without its
expectations, so a snapshot depends on Given and When alone.
-/
@[guarantee] theorem then_only_reports (j : Spec.Structure) (start : World) (sc : Scenario) :
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
@[guarantee] theorem halting_report_stops (w : World) (r : InvalidScenario) (hr : r.halts = true) : (w.report r).stopped = true := by
  simp [World.report, World.stopped, hr]

theorem foldlM_step_stopped (sc : Scenario) (xs : List (Scenario.Line × Nat)) (w : World) (h : w.stopped = true) :
    xs.foldlM (m := Id) (fun w (l, i) => w.step fsOf sc l i) w = w := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldlM_cons, World.step, h, ite_true, id_bind, id_pure]; exact ih

/-- The lines after the one that stopped the simulation take no effect. -/
@[guarantee] theorem lines_after_stop_ignored (sc : Scenario) (pre post : List (Scenario.Line × Nat)) (w : World)
    (h : (pre.foldlM (m := Id) (fun w (l, i) => w.step fsOf sc l i) w).stopped = true) :
    (pre ++ post).foldlM (m := Id) (fun w (l, i) => w.step fsOf sc l i) w =
      pre.foldlM (m := Id) (fun w (l, i) => w.step fsOf sc l i) w := by
  rw [List.foldlM_append, id_bind, foldlM_step_stopped sc post _ h]

/--
The world after `f` takes each of `xs` keeps what every take keeps: a line that names several messages acts on each.
-/
theorem forEach_keeps {α : Type} (P : World → Prop) {w : World} {xs : List α} {f : World → α → Id World}
    (hw : P w) (hf : ∀ v x, x ∈ xs → P v → P (f v x)) : P (w.forEach xs f) := by
  unfold World.forEach
  rw [foldlM_id]
  suffices ∀ (ys : List α) (v : World), (∀ y ∈ ys, y ∈ xs) → P v →
      P (ys.foldl (fun v x => if v.stopped then v else f v x) v) by
    exact this _ _ (fun y hy => hy) hw
  intro ys
  induction ys with
  | nil => intro v _ hv; exact hv
  | cons y ys ih =>
    intro v hys hv
    refine ih _ (fun z hz => hys z (List.mem_cons_of_mem _ hz)) ?_
    dsimp only
    split
    · exact hv
    · exact hf _ _ (hys y List.mem_cons_self) hv

/-- `P` holds after `f` takes each of `xs` in turn, when each take keeps it for the members of `xs`. -/
theorem foldl_mem_keeps {α β : Type} (P : β → Prop) {xs : List α} {f : β → α → β} (h : ∀ b x, x ∈ xs → P b → P (f b x))
    (b : β) (hb : P b) : P (xs.foldl f b) := by
  suffices ∀ (ys : List α), (∀ y ∈ ys, y ∈ xs) → ∀ b, P b → P (ys.foldl f b) from this xs (fun _ h => h) b hb
  intro ys
  induction ys with
  | nil => intro _ b hb; exact hb
  | cons y ys ih => intro hys b hb; exact ih (fun z hz => hys z (List.mem_cons_of_mem _ hz)) _ (h b y (hys y List.mem_cons_self) hb)

/--
Every message in flight in `w`, except those at the places that `except` names, is in flight at the same place of `w'`
with the same content, and `w'` has every place of `w`.
-/
def KeepsInFlight (except : Nat → Prop) (w w' : World) : Prop :=
  w.messages.size ≤ w'.messages.size ∧
    ∀ k msg, ¬except k → w.messages[k]? = some msg → msg.status = .inFlight → w'.messages[k]? = some msg

variable {e : Nat → Prop}

theorem keeps_refl (w : World) : KeepsInFlight e w w := ⟨Nat.le_refl _, fun _ _ _ h _ => h⟩

theorem keeps_messages {w w' w'' : World} (h : KeepsInFlight e w w') (hm : w''.messages = w'.messages) :
    KeepsInFlight e w w'' := ⟨hm ▸ h.1, fun k msg hk hw hs => by rw [hm]; exact h.2 k msg hk hw hs⟩

theorem keeps_report {w w' : World} (h : KeepsInFlight e w w') (r : InvalidScenario) : KeepsInFlight e w (w'.report r) :=
  keeps_messages h (by unfold World.report; split <;> rfl)

theorem keeps_push {w w' : World} (h : KeepsInFlight e w w') (msg : Message) :
    KeepsInFlight e w { w' with messages := w'.messages.push msg } := ⟨by have := h.1; simp only [Array.size_push]; omega,
  fun k m hk hw hs => by
    have := h.2 k m hk hw hs
    simp only [Array.getElem?_push]
    split
    · rename_i hk'
      subst hk'
      simp at this
    · exact this⟩

/-- The message `k` is one that `w` lacks, or one that `w` holds out of flight. -/
def Unkept (w : World) (k : Nat) : Prop :=
  w.messages.size ≤ k ∨ ∀ msg, w.messages[k]? = some msg → msg.status ≠ .inFlight

theorem unkept_of_keeps {w v : World} {k : Nat} (h : KeepsInFlight (fun _ => False) w v)
    (hs : ∀ msg, v.messages[k]? = some msg → msg.status ≠ .inFlight) : Unkept w k :=
  Or.inr fun msg hw hst => hs msg (h.2 k msg id hw hst) hst

theorem keeps_setStatus {w w' : World} (h : KeepsInFlight e w w') (k : Nat) (status : Status)
    (hk : e k ∨ Unkept w k) :
    KeepsInFlight e w (w'.setStatus k status) := ⟨by simp only [World.setStatus, Array.size_modify]; exact h.1,
  fun j m hj hw hs => by
    have hj' := h.2 j m hj hw hs
    unfold World.setStatus
    simp only [Array.getElem?_modify]
    split
    · rename_i hjk
      subst hjk
      rcases hk with hk | hk | hk
      · exact absurd hk hj
      · rw [Array.getElem?_eq_none hk] at hw
        cases hw
      · exact absurd hs (hk m hw)
    · exact hj'⟩

theorem keeps_post {w w' : World} (h : KeepsInFlight e w w') (o : Scenario.Origin) (sender receiver : String) (l : Line)
    (definition : Spec.Ref) : KeepsInFlight e w (w'.post o sender receiver l definition) := by
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

theorem keeps_act {w w' : World} (h : KeepsInFlight e w w') (o : Scenario.Origin) (service : String)
    (f : Service → Functions Id → State → Id State) :
    KeepsInFlight e w (w'.act fsOf o service f) := by
  unfold World.act
  split
  · exact h
  · apply keeps_route
    exact keeps_messages h rfl

theorem keeps_setStatuses {w w' : World} (h : KeepsInFlight e w w') (ks : List Nat) (status : Status)
    (hk : ∀ k ∈ ks, e k ∨ Unkept w k) :
    KeepsInFlight e w (ks.foldl (fun w k => w.setStatus k status) w') :=
  foldl_mem_keeps (KeepsInFlight e w) (fun _ k hm hv => keeps_setStatus hv k status (hk k hm)) _ h

theorem keeps_deliver {w w' : World} (h : KeepsInFlight e w w') (o : Scenario.Origin) (receiver : String)
    (ks : List Nat) (hk : ∀ k ∈ ks, e k ∨ Unkept w k) :
    KeepsInFlight e w (w'.deliver fsOf o receiver ks) := by
  unfold World.deliver
  dsimp only
  split <;> exact keeps_act (keeps_setStatuses h ks _ hk) _ _ _

theorem keeps_carry {w w' : World} (h : KeepsInFlight e w w') (i k : Nat) : KeepsInFlight e w (w'.carry i k) :=
  keeps_messages h rfl

theorem keeps_recordSent {w w' : World} (h : KeepsInFlight e w w') (i : Nat) (service : String) (before : Nat)
    (id : Option LineId) : KeepsInFlight e w (w'.recordSent i service before id) :=
  keeps_messages h (by unfold World.recordSent; (repeat' split) <;> rfl)

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
  | with_reducible refine forEach_keeps _ ?_ fun _ _ _ _ => ?_
  | dsimp only
  | split))

theorem keeps_deliverCarried {w w' : World} (h : KeepsInFlight e w w') (i : Nat) (ks : List Nat)
    (hk : ∀ k ∈ ks, e k ∨ Unkept w k) :
    KeepsInFlight e w (w'.deliverCarried fsOf i ks) := by
  unfold World.deliverCarried
  simp only [bind, pure, foldlM_id]
  have hc : KeepsInFlight e w (ks.foldl (fun w k => w.carry i k) w') :=
    foldl_keeps (KeepsInFlight e w) _ (fun v k hv => keeps_carry hv _ _) _ _ h
  refine foldl_keeps (KeepsInFlight e w) _ (fun v r hv => ?_) _ _ hc
  have hmine : ∀ k ∈ ks.filter (fun k => (v.messages[k]?).any (·.receiver == r)), e k ∨ Unkept w k :=
    fun k hm => hk k (List.mem_filter.mp hm).1
  split
  · exact hv
  · split
    · exact keeps_setStatuses hv _ _ hmine
    · refine foldl_keeps _ _ (fun u k hu => ?_) _ _ (keeps_deliver hv _ _ _ hmine)
      repeat' split
      all_goals first
        | exact hu
        | exact foldl_keeps (KeepsInFlight e w) _ (fun x l hx => keeps_recordSent hx _ _ _ _) _ _ hu

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

/-- Each of `ks` is unkept in `w` when none of them is unready and every message in flight is. -/
theorem unkept_of_findSome {w : World} {ks : List Nat} {unready : Nat → Option InvalidScenario}
    (h : ks.findSome? unready = none)
    (hu : ∀ k msg, w.messages[k]? = some msg → msg.status = .inFlight → (unready k).isSome) :
    ∀ k ∈ ks, e k ∨ Unkept w k := by
  intro k hk
  refine Or.inr (Or.inr fun msg hm hs => ?_)
  have := hu k msg hm hs
  rw [List.findSome?_eq_none_iff] at h
  rw [h k hk] at this
  cases this

theorem take_keeps (w : World) (own : String) (lines : List Scenario.Line) (i : Nat)
    (l : Scenario.Line) (hl : moved l = none) :
    KeepsInFlight (fun _ => False) w (w.take fsOf own lines i l) := by
  cases l <;> simp only [moved, reduceCtorEq] at hl <;> simp only [World.take, bind, pure, foldlM_id]
  all_goals keeps_tac
  all_goals first
    | exact keeps_clientRequest (keeps_refl _) _ _ _ _ _
    | (apply keeps_setStatus ‹KeepsInFlight _ _ _›; right
       exact unkept_of_keeps ‹KeepsInFlight _ _ _› (status_ne ‹_› ‹_› (by decide)))
    | (apply keeps_deliverCarried (keeps_refl _)
       refine unkept_of_findSome ‹_› fun k msg hm hs => ?_
       simp [hm, hs])

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
@[guarantee] theorem line_keeps_leftInFlight (w : World) (own : String) (lines : List Scenario.Line)
    (i : Nat) (l : Scenario.Line) (hl : moved l = none) :
    KeepsInFlight (fun _ => False) w (w.line fsOf own lines i l) := by
  rcases line_eq w own lines i l with h | ⟨r, -, h⟩ <;> rw [h]
  · exact take_keeps w own lines i l hl
  · exact keeps_report (keeps_refl w) r

/--
A deliver, lose, or refuse line leaves every message in flight as it is, except those its handle names.
-/
@[guarantee] theorem moving_line_keeps_others (w : World) (own : String) (lines : List Scenario.Line)
    (i : Nat) (l : Scenario.Line) (f : Scenario.Fact) (hl : moved l = some f) (ks : List Nat)
    (hk : (w.messagesOf fsOf i f).run = .ok ks) :
    KeepsInFlight (· ∈ ks) w (w.line fsOf own lines i l) := by
  rcases line_eq w own lines i l with h | ⟨r, -, h⟩ <;> rw [h]
  · cases l <;> simp only [moved, reduceCtorEq, Option.some.injEq] at hl <;> subst hl <;>
      simp only [World.take, World.resolving, bind, pure, hk]
    · split
      · exact keeps_report (keeps_refl w) _
      · exact keeps_deliverCarried (keeps_refl w) _ _ fun k hm => Or.inl hm
    · refine forEach_keeps _ (keeps_refl w) fun v k hm hv => ?_
      (repeat' split) <;> first
        | with_reducible exact hv
        | with_reducible exact keeps_report hv _
        | with_reducible exact keeps_setStatus hv _ _ (Or.inl hm)
    · split
      · refine forEach_keeps _ (keeps_refl w) fun v k hm hv => ?_
        (repeat' split) <;> first
          | with_reducible exact hv
          | with_reducible exact keeps_report hv _
          | with_reducible exact keeps_push (keeps_setStatus hv _ _ (Or.inl hm)) _
      · refine keeps_deliverCarried (forEach_keeps _ (keeps_refl w) fun v k hm hv => ?_) _ _
          fun k' hk' => Or.inr (Or.inl ?_)
        · (repeat' split) <;> first
            | with_reducible exact hv
            | with_reducible exact keeps_report hv _
            | with_reducible exact keeps_push (keeps_setStatus hv _ _ (Or.inl hm)) _
        · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hk'
          omega
  · exact keeps_report (keeps_refl w) r

theorem overtaken_halts {w : World} {i : Nat} {ks : List Nat} {k : Nat} {r : InvalidScenario}
    (h : w.overtaken i ks k = some r) : r.halts = true := by
  unfold World.overtaken at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, h⟩ := h
  cases h; rfl

/--
A deliver line any of whose messages has an earlier message in flight that the line does not name and that must arrive
first (World.precedes) delivers nothing and stops the simulation with a violation: ordered messages on one channel reach
their receiver in sending order. A line that names both delivers them in one processing.
-/
@[guarantee] theorem overtaking_delivery_halts (w : World) (own : String) (lines : List Scenario.Line)
    (i : Nat) (f : Scenario.Fact) (ks : List Nat) (k : Nat) (msg : Message)
    (hk : (w.messagesOf fsOf i f).run = .ok ks) (hkm : k ∈ ks) (hm : w.messages[k]? = some msg)
    (j : Nat) (n : Message) (hj : j < k) (hjk : j ∉ ks) (hn : w.messages[j]? = some n)
    (hs : n.status = .inFlight) (hc : w.precedes n msg = true) :
    ∃ r, r.halts = true ∧ w.line fsOf own lines i (.deliver f) = w.report r := by
  rcases line_eq w own lines i (.deliver f) with h | h
  · rw [h]
    simp only [World.take, World.resolving, bind, pure, hk]
    split
    · rename_i r hr
      refine ⟨r, ?_, rfl⟩
      obtain ⟨k', -, hk'⟩ := List.exists_of_findSome?_eq_some hr
      obtain ⟨msg', -, hr'⟩ := Option.bind_eq_some_iff.mp hk'
      split at hr'
      · cases hr'; rfl
      · exact overtaken_halts hr'
    · rename_i hnone
      exfalso
      have hmem : (n, j) ∈ w.messages.toList.zipIdx.take k :=
        List.mem_iff_getElem?.mpr ⟨j, by simp [hj, hn]⟩
      have hfind : ((w.messages.toList.zipIdx.take k).find? fun x =>
          !ks.contains x.2 && x.1.status == .inFlight && w.precedes x.1 msg).isSome :=
        List.find?_isSome.mpr ⟨(n, j), hmem, by simp_all⟩
      obtain ⟨⟨earlier, je⟩, he⟩ := Option.isSome_iff_exists.mp hfind
      have := List.findSome?_eq_none_iff.mp hnone k hkm
      rw [hm] at this
      by_cases hst : msg.status = .inFlight
      · simp [World.overtaken, hm, hst] at this
        exact this earlier je (by simpa using he)
      · simp [hst] at this
  · exact h

theorem foldl_stopped {α : Type} {v : World} {xs : List α} {f : World → α → Id World} (h : v.stopped = true) :
    xs.foldl (fun v x => if v.stopped = true then pure v else f v x) v = v := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [List.foldl_cons, h, ite_true]; exact ih

/-- The world after `f` takes each of `xs` stops when `f` stops it at one of them, while `P` holds before each take. -/
theorem forEach_hits {α : Type} (P : World → Prop) {xs : List α} {f : World → α → Id World} {x : α} (hx : x ∈ xs)
    (hP : ∀ v y, P v → v.stopped = false → P (f v y)) (hs : ∀ v, P v → v.stopped = false → (f v x).stopped = true)
    {w : World} (hw : P w) : (w.forEach xs f).stopped = true := by
  unfold World.forEach
  rw [foldlM_id]
  induction xs generalizing w with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    by_cases hst : w.stopped = true
    · simp only [hst, ite_true]
      exact (congrArg World.stopped (foldl_stopped (xs := ys) (f := f) hst)).trans hst
    · simp only [hst, Bool.false_eq_true, ite_false]
      have hst' : w.stopped = false := by simpa using hst
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (congrArg World.stopped (foldl_stopped (xs := ys) (f := f) (hs w hw hst'))).trans (hs w hw hst')
      · exact ih hx (hP w y hw hst')

/-- Whether `w` holds `msg` at place `k`, and `peer` is external in `w`. -/
def Holds (k : Nat) (msg : Message) (peer : String) (w : World) : Prop :=
  w.messages[k]? = some msg ∧ w.role peer = some .external

theorem holds_report {k : Nat} {msg : Message} {peer : String} {w : World} (h : Holds k msg peer w)
    (r : InvalidScenario) : Holds k msg peer (w.report r) := by
  unfold World.report; split <;> exact h

theorem holds_stated {k : Nat} {msg : Message} {peer : String} {w : World} (h : Holds k msg peer w) (i : Nat)
    (m : Message) : Holds k msg peer (w.stated i m) := by
  unfold World.stated
  split
  · exact holds_report h _
  · refine ⟨?_, h.2⟩
    have hk : k < w.messages.size := by
      have := h.1; rw [Array.getElem?_eq_some_iff] at this; exact this.1
    simp only [World.carry, Array.getElem?_push, Nat.ne_of_lt hk, ite_false]
    exact h.1

/--
An external peer's answer line names requests that reached that peer: when any it takes did not, the simulation stops.
-/
@[guarantee] theorem external_answer_needs_delivery (w : World) (own : String) (lines : List Scenario.Line)
    (i : Nat) (peer : String) (f : Scenario.Fact) (a : Scenario.Template) (ks : List Nat) (k : Nat)
    (msg : Message) (hr : w.role peer = some .external)
    (hk : (w.messagesOf fsOf i f).run = .ok ks) (hkm : k ∈ ks)
    (hm : w.messages[k]? = some msg) (hd : ¬(msg.receiver = peer ∧ msg.status = .delivered)) :
    (w.line fsOf own lines i (.answer peer f a)).stopped = true := by
  rcases line_eq w own lines i (.answer peer f a) with h | h
  · rw [h]
    simp only [World.take, World.resolving, bind, pure, hk]
    refine forEach_hits (Holds k msg peer) hkm (fun v y hv _ => ?_) (fun v hv hst => ?_) ⟨hm, hr⟩
    · simp only [hv.2]
      (repeat' split) <;> first
        | exact hv
        | exact holds_report hv _
        | exact holds_stated (by unfold World.nextId; exact hv) _ _
    · simp only [hv.1, hv.2]
      by_cases hrec : msg.receiver = peer
      · have hst' : msg.status ≠ .delivered := fun e => hd ⟨hrec, e⟩
        simp [hrec, hst', World.report, World.stopped, InvalidScenario.halts]
      · simp [hrec, World.report, World.stopped, InvalidScenario.halts]
  · obtain ⟨r, hh, e⟩ := h
    rw [e]; simp [World.report, World.stopped, hh]

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
  | with_reducible refine forEach_keeps _ ?_ fun _ _ _ _ => ?_
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
@[guarantee] theorem line_keeps_states (w : World) (own : String) (lines : List Scenario.Line) (i : Nat) (l : Scenario.Line)
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
/-- An answer that arrives again with the id of an earlier one is written and not processed again. -/
@[guarantee] theorem redelivered_answer_not_processed (st : Service) (fs : Functions Id) (s : State) (id to : LineId) (a : Answer)
    (hd : id ∈ s.deliveries) :
    answerIn st fs s id to a = message st fs (s.write .in (some id) (.answer to a)).1.newMessage {} := by
  simp [answerIn, hd]

/-- An answer to a request that waits no more, as after a restart, is written and has no other effect. -/
@[guarantee] theorem late_answer_written (st : Service) (fs : Functions Id) (s : State) (id to : LineId) (a : Answer)
    (hd : id ∉ s.deliveries) (hp : s.pending.find? (·.id == to) = none) :
    answerIn st fs s id to a =
      message st fs ({ s with deliveries := s.deliveries ++ [id] }.write .in (some id) (.answer to a)).1.newMessage {} := by
  simp [answerIn, hd, hp]


/--
A refuse line that names one request in flight answers the sender `unavailable`: the request is lost, and the line
delivers the `refusal`, an `unavailable` answer in flight from the receiver to the sender.
-/
@[guarantee] theorem refuse_answers_unavailable (w : World) (own : String) (lines : List Scenario.Line) (i : Nat)
    (f : Scenario.Fact) (k : Nat) (msg : Message) (hk : (w.messagesOf fsOf i f).run = .ok [k])
    (hm : w.messages[k]? = some msg) (hs : msg.status = .inFlight) (ht : (requestTarget? msg.body).isSome = true)
    (hw : w.stopped = false) :
    w.take fsOf own lines i (.refuse f) =
      let w' := w.setStatus k .lost
      { w' with messages := w'.messages.push (refusal msg i) }.deliverCarried fsOf i [w.messages.size] := by
  have hn : (requestTarget? msg.body).isNone = false := by simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using ht
  simp only [World.take, World.resolving, World.forEach, bind, pure, hk, foldlM_id, List.foldl_cons, List.foldl_nil,
    hw, Bool.false_eq_true, ite_false, hm, hs, hn]
  have hw' : w.halted.isSome = false ∧ (w.states.any fun x => x.2.halted.isSome) = false := by
    simpa [World.stopped] using hw
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, World.stopped, hw'.1, hw'.2, Bool.or_false,
    World.setStatus, Array.size_push, Array.size_modify, Nat.add_sub_cancel_left, List.range_one, List.map_cons,
    List.map_nil, Nat.add_zero]

/-- A running service whose state reported a halting `Fault` or `InvalidInput` stops the simulation. -/
@[guarantee] theorem halting_finding_stops (w : World) (q : String) (s : State) (f : Finding)
    (hm : (q, s.report f) ∈ w.states) (hf : f.halts = true) : w.stopped = true := by
  simp only [World.stopped, Bool.or_eq_true, List.any_eq_true]
  exact Or.inr ⟨_, hm, by simp [Tazuna.Thm.Service.State.report_halted f hf]⟩

/-- A run that stopped gets no checks of the exchanges with external services. -/
@[guarantee] theorem stopped_run_skips_exchanges (w : World) (h : w.stopped = true) : w.ended fsOf = w := by
  simp [World.ended, h]

/--
A clock line publishes the subscription answers that the new time changes: after the due deadlines fire, a running
service that did not halt writes the time line and publishes.
-/
@[guarantee] theorem clock_publishes (time : Time) (st : Service) (fs : Functions Id) (s : State)
    (h : (observeResponses st fs ((fireDue st fs time Limit.dueDeadlines.max none s).passTime st time)).halted = none) :
    fireTo time st fs s =
      publish st fs ((observeResponses st fs ((fireDue st fs time Limit.dueDeadlines.max none s).passTime st time)).write
        .in none .time).1 := by
  simp [fireTo, h]

end Tazuna.Thm.Sim.Run
