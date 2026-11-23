import Tazuna.Service.Query
import Tazuna.Thm.Service.State
import Tazuna.Thm.Guarantee

namespace Tazuna.Thm.Service.Query

open Tazuna.Data Tazuna.Service
open Tazuna.Thm.Data.Basic Tazuna.Thm.Service.State Tazuna.Thm.Spec.Shape Tazuna.Thm.Service.Chart.Basic

variable {st : Service} {fs : Functions Id} {s : State}

theorem publishOne_fixed (t : State) (sub : Subscription) : (publishOne st fs t sub).fixed = t.fixed := by
  unfold publishOne
  split
  · rfl
  · simp only [id_bind]
    split
    · exact report_fixed ..
    · split
      · simp
      · split
        · exact reportAll_fixed _
        · exact reportAll_fixed (s := t) _

theorem publish_fixed : (publish st fs s).fixed = s.fixed := by
  unfold publish
  rw [foldlM_id]
  exact foldl_fixed _ publishOne_fixed _ _

theorem publish_grows : Grows s (publish st fs s) := by
  unfold publish
  rw [foldlM_id]
  refine foldl_grows _ (fun t sub => ?_) (fun t sub => congrArg Fixed.now (publishOne_fixed t sub)) _ _
  unfold publishOne
  split
  · exact Grows.refl _
  · simp only [id_bind]
    split
    · exact Grows.of_lines (report_lines ..)
    · split
      · exact Grows.of_lines (by simp)
      · split
        · exact Grows.of_lines (reportAll_lines _)
        · exact (Grows.of_lines (reportAll_lines (s := t) _)).trans (reportAll_now (s := t) _) (grows_write _ _ _ _ _ _)

@[guarantee] theorem changed_answer_sent (sub : Subscription) (a : Answer) (vs : List Fault) (c : Value)
    (hh : s.halted = none) (hr : resolveChecked st fs s sub.query sub.input sub.caller = .answered a vs)
    (hc : fs.comparable sub.query a = .ok c) (hl : sub.last ≠ some c) :
    publishOne st fs s sub =
      ({ s.reportAll vs with subscriptions := s.subscriptions.map fun (u : Subscription) =>
          if u.id == sub.id then { u with last := some c } else u }.write .out none (.answer sub.id a) () () (st.ref sub.query)).1 := by
  simp [publishOne, hh, hr, hc, hl]

@[guarantee] theorem unchanged_answer_not_sent (sub : Subscription) (a : Answer) (vs : List Fault) (c : Value)
    (hh : s.halted = none) (hr : resolveChecked st fs s sub.query sub.input sub.caller = .answered a vs)
    (hc : fs.comparable sub.query a = .ok c) (hl : sub.last = some c) :
    publishOne st fs s sub = s.reportAll vs := by
  have : (sub.last == some c) = true := by rw [hl]; exact beq_self_eq_true _
  simp only [publishOne, hh, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, id_bind, hr, hc, this]
  rfl

theorem publishOne_adds_answer (sub : Subscription) :
    AddsOnly (fun l => l.dir = .out ∧ ∃ a, l.body = .answer sub.id a) s (publishOne st fs s sub) := by
  unfold publishOne
  split
  · exact ⟨#[], by simp, by simp⟩
  · simp only [id_bind]
    split
    · exact ⟨#[], by simp, by simp⟩
    · split
      · exact ⟨#[], by simp, by simp⟩
      · split
        · exact ⟨#[], by show (s.reportAll _).lines = _; simp, by simp⟩
        · exact ⟨#[_], by show (s.reportAll _).lines.push _ = _; rw [reportAll_lines, Array.push_eq_append], by
            intro l hl'
            simp only [Array.mem_singleton] at hl'
            subst hl'
            exact ⟨rfl, _, rfl⟩⟩

theorem publish_answers_only_open_subscriptions :
    AddsOnly (fun l => l.dir = .out ∧ ∃ sub ∈ s.subscriptions, ∃ a, l.body = .answer sub.id a) s (publish st fs s) := by
  unfold publish
  rw [foldlM_id]
  have key : ∀ (subs : List Subscription) (t : State), (∀ sub ∈ subs, sub ∈ s.subscriptions) →
      AddsOnly (fun l => l.dir = .out ∧ ∃ sub ∈ s.subscriptions, ∃ a, l.body = .answer sub.id a) t
        (subs.foldl (publishOne st fs) t) := by
    intro subs
    induction subs with
    | nil => intro t _; exact ⟨#[], by simp, by simp⟩
    | cons sub subs ih =>
      intro t hsub
      simp only [List.foldl_cons]
      refine AddsOnly.trans ?_ (ih _ fun x hx => hsub x (List.mem_cons_of_mem _ hx))
      obtain ⟨n, e, p⟩ := publishOne_adds_answer (st := st) (fs := fs) (s := t) sub
      refine ⟨n, e, fun l hl => ?_⟩
      obtain ⟨hd, a, ha⟩ := p l hl
      exact ⟨hd, sub, hsub sub (List.mem_cons_self ..), a, ha⟩
  exact key _ _ fun _ h => h

@[guarantee] theorem ended_subscription_not_answered (id : LineId) (hid : ∀ sub ∈ s.subscriptions, sub.id ≠ id) :
    ∃ new, (publish st fs s).lines = s.lines ++ new ∧ ∀ l ∈ new, ∀ a, l.body ≠ .answer id a := by
  obtain ⟨new, e, p⟩ := publish_answers_only_open_subscriptions (st := st) (fs := fs) (s := s)
  refine ⟨new, e, fun l hl a ha => ?_⟩
  obtain ⟨_, sub, hsub, b, hb⟩ := p l hl
  rw [ha] at hb
  injection hb with h
  exact hid sub hsub h.symm

@[guarantee] theorem query_invalid_input_rejected (name : String) (raw : Value) (caller : Caller)
    (hp : fs.parseOutside st (.input (st.ref name)) raw = .ok none) :
    resolveChecked st fs s name raw caller = .answered (.rejected { kind := .invalidInput }) [] := by
  simp [resolveChecked, hp]

@[guarantee] theorem resolve_output_answered (name : String) (raw input output : Value) (caller : Caller)
    (failed : Option String) (rq : Requirements) (hp : fs.parseOutside st (.input (st.ref name)) raw = .ok (some input))
    (hq : st.requirements.lookup name = some rq)
    (hc : (callerRejection st s.records (st.ref name) rq.callers caller : Id _) = none)
    (hr : firstFalse (fs.inputRequirement (st.ref name) · input) rq.requires = .ok none)
    (hv : fs.resolve name input caller s.records s.now = .ok output)
    (he : fs.queryEnsures name input caller output s.records = .ok failed) :
    ∃ vs, resolveChecked st fs s name raw caller = .answered (.fulfilled output) vs := by
  cases failed <;> simp [resolveChecked, expectFound, hp, hq, hc, hr, hv, he] <;> exact ⟨_, rfl⟩

end Tazuna.Thm.Service.Query
