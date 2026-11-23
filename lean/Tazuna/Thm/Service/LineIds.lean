import Std.Data.String.ToNat
import Tazuna.Service.Restart
import Tazuna.Thm.Data.Basic
import Tazuna.Thm.Service.Note
import Tazuna.Thm.Service.Now

/-!
The ids of a service's own lines: every input keeps the lines before it and numbers each `out` line it writes as
State.write does, so no two `out` lines carry one id.
-/

namespace Tazuna.Thm.Service.LineIds

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.Note Tazuna.Thm.Service.State Tazuna.Thm.Service.Chart.Queue
open Tazuna.Thm.Service.Chart.Macrostep Tazuna.Thm.Service.Command Tazuna.Thm.Service.Queue Tazuna.Thm.Service.Clock
open Tazuna.Thm.Service.Now

theorem first_inj {c : Char} {as bs as' bs' : List Char} (ha : c ∉ as) (ha' : c ∉ as')
    (h : as ++ c :: bs = as' ++ c :: bs') : as = as' ∧ bs = bs' := by
  induction as generalizing as' with
  | nil => cases as' with
    | nil => simpa using h
    | cons a as' => simp at h ha'; exact absurd h.1 ha'.1
  | cons a as ih => cases as' with
    | nil => simp at h ha; exact absurd h.1.symm ha.1
    | cons a' as' =>
      simp only [List.cons_append, List.cons.injEq] at h
      simp only [List.mem_cons, not_or] at ha ha'
      obtain ⟨rfl, h⟩ := h
      have := ih ha.2 ha'.2 h
      exact ⟨by rw [this.1], this.2⟩

theorem hash_not_mem_repr (n : Nat) : '#' ∉ (Nat.repr n).toList := by
  intro h
  have := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (by decide) (by decide) (by simpa [Nat.toList_repr] using h)
  simp at this

/-- A numbered id names its line name and its number: the number has no `#`, so the last `#` divides them. -/
theorem numbered_inj {x y : String} {a b : Nat} (h : s!"{x}#{a}" = s!"{y}#{b}") : x = y ∧ a = b := by
  change x ++ "#" ++ Nat.repr a = y ++ "#" ++ Nat.repr b at h
  have h := congrArg (fun s => s.toList.reverse) h
  simp only [String.toList_append, List.reverse_append, List.append_assoc] at h
  have hs : "#".toList.reverse = ['#'] := by decide
  rw [hs, List.singleton_append, List.singleton_append] at h
  have := first_inj (hash_not_mem_repr a ∘ List.mem_reverse.mp) (hash_not_mem_repr b ∘ List.mem_reverse.mp) h
  exact ⟨String.toList_injective (List.reverse_inj.mp this.2),
    Nat.repr_injective (String.toList_injective (List.reverse_inj.mp this.1))⟩

/--
Two `out` lines of numbered lines carry different ids: of one name, the later counts the earlier among the lines before
it, so its number is larger.
-/
theorem numbered_ids_distinct {service : String} {lines : Array Line} (h : Numbered service lines) {i j : Nat}
    (hij : i < j) (hj : j < lines.size) (hi : lines[i].dir = .out) (hj' : lines[j].dir = .out) :
    lines[i].id ≠ lines[j].id := by
  have hi' : i < lines.size := by omega
  have take : ∀ k (hk : k < lines.size), lines.toList.take (k + 1) = lines.toList.take k ++ [lines[k]] := fun k hk => by
    rw [List.take_succ_eq_append_getElem (by simpa using hk), Array.getElem_toList]
  have pre : ∀ k (hk : k < lines.size), lines.toList.take k ++ [lines[k]] <+: lines.toList := fun k hk => by
    rw [← take k hk]; exact List.take_prefix _ _
  rw [h _ _ (pre i hi') hi, h _ _ (pre j hj) hj']
  intro he
  obtain ⟨hn, hc⟩ := numbered_inj (LineId.own.inj he)
  have hle : lines.toList.take i ++ [lines[i]] <+: lines.toList.take j := by
    rw [← take i hi']
    exact List.take_prefix_take_left (by omega : i + 1 ≤ j)
  have := hle.sublist.countP_le (p := (·.body.idName service == lines[j].body.idName service))
  simp only [namedCount, ← Array.countP_toList, List.countP_append] at hc this
  simp only [hn] at hc
  simp [hn] at this
  omega

/-- `t` keeps the lines of `s` first, and numbers its `out` lines as State.write does when `s` does. -/
def KeepsIds (s t : State) : Prop :=
  s.lines.toList <+: t.lines.toList ∧ (Numbered s.service s.lines → Numbered t.service t.lines)

theorem KeepsIds.refl (s : State) : KeepsIds s s := ⟨List.prefix_refl _, id⟩

theorem KeepsIds.trans {a b c : State} (h₁ : KeepsIds a b) (h₂ : KeepsIds b c) : KeepsIds a c :=
  ⟨h₁.1.trans h₂.1, h₂.2 ∘ h₁.2⟩

theorem KeepsIds.of_lines {s t : State} (h : t.lines = s.lines) (hs : t.service = s.service := by first | rfl | simp) :
    KeepsIds s t :=
  ⟨by rw [h]; exact List.prefix_refl _, by rw [h, hs]; exact id⟩

theorem _root_.Tazuna.Thm.Service.State.Grows.keepsIds {s t : State} (h : Grows s t) : KeepsIds s t := by
  obtain ⟨⟨new, e, -⟩, m⟩ := h
  exact ⟨by rw [e]; simp, m⟩

variable {st : Service} {fs : Functions Id}

/--
Closes `KeepsIds s t` where `t` is `s` with lines written, and fields other than the lines and the service changed;
each `out` line is written without an id.
-/
macro "ids_leaf" : tactic => `(tactic| (refine ⟨?_, ?_⟩ <;> simp [KeepsIds, State.write, State.lineId,
  State.newMessage, State.newStep, State.answer, State.halt, State.violate, numbered_push, LineBody.idName,
  apply_ite State.lines, apply_ite State.toDurable, apply_ite Durable.service] <;> (repeat' split) <;>
  simp_all [numbered_push]) <;> done)

theorem growsBy_deliverAnswer (step : Nat) (p : Pending) (answer : Answer) :
    GrowsBy (deliverAnswer fs st step p answer) := by
  intro r
  unfold deliverAnswer
  dsimp only
  have hl : (r.state.answered p).1.lines = r.state.lines := by simp [State.answered]; split <;> rfl
  have hs : (r.state.answered p).1.service = r.state.service := by simp [State.answered]; split <;> rfl
  have hn : (r.state.answered p).1.now = r.state.now := by simp [State.answered]; split <;> rfl
  split
  · exact Grows.after (growsBy_answerTo _ _ _ _) hl hn hs
  · exact Grows.of_lines hl hs

theorem keepsIds_fireDue (to : Time) (fuel : Nat) (tie : Option Time) (s : State) :
    KeepsIds s (fireDue st fs to fuel tie s) := by
  induction fuel generalizing s tie with
  | zero => simp only [fireDue]; split <;> exact .of_lines (by simp)
  | succ fuel ih =>
    rw [fireDue]
    split
    · exact .refl _
    · split
      · exact .refl _
      · dsimp only
        split
        · exact .of_lines (report_lines _)
        · rename_i hc
          obtain ⟨_, rfl⟩ := chooseDeadline_orders hc
          simp only [id_bind, note_id, endMessage_id]
          refine KeepsIds.trans ?_ (ih _ _)
          refine KeepsIds.trans ?_ Tazuna.Thm.Service.Response.observeResponses_grows.keepsIds
          refine KeepsIds.trans ?_ afterMessage_grows.keepsIds
          refine KeepsIds.trans ?_ (drain_grows _ _).keepsIds
          refine KeepsIds.trans ?_ (growsBy_settled _ _ (growsBy_fire _ _) (keeps_fire _ _) _).keepsIds
          exact .of_lines (by simp [State.newMessage, State.newStep]) (by simp [State.newMessage, State.newStep])

theorem keepsIds_message (s : State) (q : Queue) : KeepsIds s (message st fs s q) := by
  simp only [message, finish, id_bind, endMessage_id]
  exact ((drain_grows _ _).trans (drain_keeps_now _ _) afterMessage_grows).keepsIds.trans
    (Tazuna.Thm.Service.Response.observeResponses_grows.keepsIds.trans (keepsIds_fireDue _ _ _ _))

theorem keepsIds_send (name : Spec.Ref) (id : Option LineId) (raw : Value) (s : State) :
    KeepsIds s (send st fs s name id raw) := by
  simp only [send, id_bind]
  repeat' split
  all_goals first
    | ids_leaf
    | (refine KeepsIds.trans ?_ (keepsIds_message _ _); ids_leaf)
    | (refine KeepsIds.trans ?_ (keepsIds_message _ _)
       refine KeepsIds.trans ?_ (Grows.of_lines (s' := { (processCommand st fs _ _ _ _ _).1 with commandAnswers := _ })
         rfl rfl).keepsIds
       refine KeepsIds.trans ?_ (processCommand_grows _ _ _ _).keepsIds
       ids_leaf)

theorem keepsIds_call (name : Spec.Ref) (id : Option LineId) (raw : Value) (s : State) :
    KeepsIds s (call st fs s name id raw) := by
  simp only [call, id_bind]
  repeat' split
  all_goals first
    | ids_leaf
    | (refine KeepsIds.trans ?_ (keepsIds_message _ _); ids_leaf)

theorem keepsIds_subscribe (name : Spec.Ref) (id : Option LineId) (raw : Value) (s : State) :
    KeepsIds s (subscribe st fs s name id raw) := by
  simp only [subscribe]
  repeat' split
  all_goals first
    | ids_leaf
    | (refine KeepsIds.trans ?_ (keepsIds_message _ _); ids_leaf)

theorem keepsIds_endSubscription (id : LineId) (s : State) : KeepsIds s (endSubscription st fs s id) := by
  simp only [endSubscription]
  refine KeepsIds.trans ?_ (keepsIds_message _ _)
  ids_leaf

theorem keepsIds_receive (name : Spec.Ref) (id : LineId) (raw : Value) (resultOf : Option LineId) (s : State) :
    KeepsIds s (receive st fs s name id raw resultOf) := by
  simp only [receive, redeliver, deliver, id_bind]
  repeat' split
  all_goals first
    | ids_leaf
    | (refine KeepsIds.trans ?_ (keepsIds_message _ _); ids_leaf)

theorem keepsIds_answerRequest (id : Option LineId) (p : Pending) (answer : Answer) (s : State) :
    KeepsIds s (answerRequest st fs s id p answer) := by
  simp only [answerRequest, id_bind]
  repeat' split
  all_goals first
    | ids_leaf
    | (refine KeepsIds.trans ?_ (keepsIds_message _ _)
       refine KeepsIds.trans ?_ (growsBy_settled _ _ (growsBy_deliverAnswer _ _ _) (keeps_deliverAnswer _ _ _) _).keepsIds
       ids_leaf)

theorem keepsIds_begin (s : State) : KeepsIds s (begin st fs s) := by
  simp only [begin, id_bind]
  split
  · exact .refl _
  · refine KeepsIds.trans ?_ (keepsIds_message _ _)
    have hr : ∀ t : State, (startRecords st fs t).lines = t.lines ∧ (startRecords st fs t).service = t.service :=
      fun t => by
        simp only [startRecords]; rw [foldlM_id]
        exact foldl_keeps (fun x : State => x.lines = t.lines ∧ x.service = t.service) _
          (fun x e hx => by split <;> simp [hx]) _ _ ⟨rfl, rfl⟩
    have hi : ∀ t : State, (startInstances st fs t).lines = t.lines ∧ (startInstances st fs t).service = t.service :=
      fun t => by
        simp only [startInstances]; rw [foldlM_id]
        exact foldl_keeps (fun x : State => x.lines = t.lines ∧ x.service = t.service) _ (fun x c hx => by
          simp only [startInstance, id_bind]; (repeat' split) <;> simp [hx]) _ _ ⟨rfl, rfl⟩
    refine KeepsIds.trans (KeepsIds.of_lines (t := { s with started := true }.newMessage) rfl) ?_
    exact .of_lines ((hi _).1.trans (hr _).1) ((hi _).2.trans (hr _).2)

theorem keepsIds_operate (screen : InstanceId) (control : String) (payload : Value) (s : State) :
    KeepsIds s (operate st fs s screen control payload) := by
  simp only [operate, id_bind]
  repeat' split
  all_goals first
    | ids_leaf
    | (refine KeepsIds.trans ?_ (keepsIds_message _ _)
       refine KeepsIds.trans ?_ (growsBy_settled _ _ (growsBy_dispatch _ _ _ _) (keeps_dispatch _ _ _ _) _).keepsIds
       ids_leaf)

theorem keepsIds_restart (s : State) : KeepsIds s (restart st fs s) := by
  simp only [restart]
  refine KeepsIds.trans ?_ (keepsIds_begin _)
  exact (grows_write (s := s) .in none .restart () () ()).keepsIds.trans (.of_lines rfl)

end Tazuna.Thm.Service.LineIds
