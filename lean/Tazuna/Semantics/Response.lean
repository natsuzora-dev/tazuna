import Tazuna.Semantics.Valid

/-! What a response means: "after each event `trigger` satisfying `after`, an event satisfying
`then(trigger, event)` within `within` ms". A run violates it when some step applies an `after` event and a later step
comes past the deadline with no step from the first one up to it applying an event that `then` ties to that trigger.
Each trigger is judged on its own, so two `after` events in one step make two deadlines. A response is judged per
step: a `then` event in the same step as its trigger counts, whatever their order inside the step, since that order is
the semantics' canonical one and a verdict resting on it would rest on an order the spec does not write. A run that
ends before the deadline does not violate. Time is the state's after each step: a clock line's events carry the clock
line's time.

A response is proved by induction over steps (Lamport, "Real Time is Really Simple", sec 3.3): the records keep a
deadline for each trigger that waits (`deadlineAt`). Where every step of a run opens each trigger it does not answer
with a deadline in time, keeps the deadline of each waiting trigger it does not answer no later, and moves time past
no waiting deadline, the run does not violate the response (`not_violated`). -/

namespace Tazuna.Ir

/-- What a response reads of one step of a run: its time, and the events it applied. -/
structure Moment (e : Ty) where
  time : Int
  events : List e.den0

/-- A step's moment: the time after it and the events it applied. -/
def Result.moment {v : ServiceV} (r : Result v) : Moment v.event := ⟨r.state.now, r.events⟩

/-- An `Option(Int)` value as a Lean option. -/
def Step.optionInt : (Ty.option Ty.int).den0 → Option Int
  | .inl (d, ()) => some (show Int from d)
  | .inr _ => none

namespace ResponseV

variable {r e : Ty} (resp : ResponseV r e)

/-- Whether the event satisfies `after`. -/
def opens (ev : e.den0) : Bool := Step.toB (resp.after.fn (ev, ()))

/-- Whether a step applies an event that `then` ties to `trigger`. -/
def answers (trigger : e.den0) (m : Moment e) : Bool := m.events.any fun ev => Step.toB (resp.then_.fn (trigger, ev, ()))

/-- The run's steps `ms` violate the response: step `i` applies a trigger satisfying `after`, a later step `j` comes
past `i`'s time plus `within`, and no step from `i` up to (not including) `j` answers that trigger. -/
def Violated (ms : List (Moment e)) : Prop :=
  ∃ i j trigger, ∃ (hij : i < j) (hj : j < ms.length), trigger ∈ ms[i].events ∧ resp.opens trigger = true ∧
    ms[j].time > ms[i].time + (resp.withinNat : Int) ∧ ∀ m (_ : i ≤ m) (hm : m < j), resp.answers trigger ms[m] = false

/-- Whether some step of `ms` comes past `t0 + within` with no step before it answering `trigger`. -/
def late (trigger : e.den0) (t0 : Int) : List (Moment e) → Bool
  | [] => false
  | m :: ms => decide (m.time > t0 + (resp.withinNat : Int)) || (!resp.answers trigger m && late trigger t0 ms)

/-- `Violated`, computed. -/
def violated : List (Moment e) → Bool
  | [] => false
  | m :: ms => m.events.any (fun ev => resp.opens ev && !resp.answers ev m && resp.late ev m.time ms) || violated ms

theorem late_iff (trigger : e.den0) (t0 : Int) : (ms : List (Moment e)) → (resp.late trigger t0 ms = true ↔
    ∃ j, ∃ (hj : j < ms.length), ms[j].time > t0 + (resp.withinNat : Int) ∧
      ∀ m (hm : m < j), resp.answers trigger ms[m] = false)
  | [] => by simp [late]
  | m :: ms => by
    simp only [late, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', late_iff trigger t0 ms]
    constructor
    · rintro (h | ⟨hq, j, hj, ht, hm⟩)
      · exact ⟨0, by simp, h, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      · refine ⟨j + 1, by simpa using hj, ht, fun k hk => ?_⟩
        cases k with
        | zero => exact hq
        | succ k => exact hm k (by omega)
    · rintro ⟨j, hj, ht, hm⟩
      cases j with
      | zero => exact .inl ht
      | succ j => exact .inr ⟨hm 0 (by omega), j, by simpa using hj, ht, fun k hk => hm (k + 1) (by omega)⟩

/-- The computed form is the meaning. -/
theorem violated_iff : (ms : List (Moment e)) → (resp.violated ms = true ↔ resp.Violated ms)
  | [] => by simp [violated, Violated]
  | m :: ms => by
    simp only [violated, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', violated_iff ms,
      late_iff]
    constructor
    · rintro (⟨ev, hev, ⟨hp, hq⟩, j, hj, ht, hm⟩ | ⟨i, j, ev, hij, hj, hev, hp, ht, hm⟩)
      · refine ⟨0, j + 1, ev, by omega, by simpa using hj, hev, hp, ht, fun k _ hk => ?_⟩
        cases k with
        | zero => exact hq
        | succ k => exact hm k (by omega)
      · exact ⟨i + 1, j + 1, ev, by omega, by simpa using hj, hev, hp, ht, fun k hk hkj => by
          obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          exact hm k (by omega) (by omega)⟩
    · rintro ⟨i, j, ev, hij, hj, hev, hp, ht, hm⟩
      cases i with
      | zero =>
        obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        exact .inl ⟨ev, hev, ⟨hp, hm 0 (Nat.le_refl _) hij⟩, j, by simpa using hj, ht,
          fun k hk => hm (k + 1) (by omega) (by omega)⟩
      | succ i =>
        obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        exact .inr ⟨i, j, ev, by omega, by simpa using hj, hev, hp, ht, fun k hk hkj => hm (k + 1) (by omega) (by omega)⟩

/-- The deadline the records keep for the trigger, as `deadline` gives it: none once the trigger waits no more. -/
def deadlineAt (records : r.den0) (tr : e.den0) : Option Int := Step.optionInt (resp.deadline.fn (records, tr, ()))

end ResponseV

section
variable {v : ServiceV} (T : List TypeDecl) (resp : ResponseV v.records v.event) (F : v.records.den0 → Prop)
  (G : v.event.den0 → Prop)

/-- What the induction reads of one step from `s` on `x`, with `F` the records where the waiting parts are known and
`G` the triggers they are known of: each event the step applies is in `G`, and each trigger it applies and does not
answer has a deadline in time after it (`opens`); where `F` holds before it, each waiting trigger in `G` it does not
answer still waits with a deadline no later (`waits`), and the step leaves time as it was or at most at each waiting
deadline (`clock`); and `F` holds after it where it held before or the step applied an event (`fits`). -/
structure ResponseV.Keeps (s : State v) (x : Input v) : Prop where
  opens : ∀ ev ∈ (step T v s x).events, G ev ∧ (resp.opens ev = true → resp.answers ev (step T v s x).moment = false →
    ∃ d, resp.deadlineAt (step T v s x).state.records ev = some d ∧
      d ≤ (step T v s x).state.now + (resp.withinNat : Int))
  waits : F s.records → ∀ tr d, G tr → resp.deadlineAt s.records tr = some d →
    resp.answers tr (step T v s x).moment = false →
    ∃ d', resp.deadlineAt (step T v s x).state.records tr = some d' ∧ d' ≤ d
  clock : F s.records → ∀ tr d, G tr → resp.deadlineAt s.records tr = some d →
    (step T v s x).state.now ≤ d ∨ (step T v s x).state.now = s.now
  fits : F s.records ∨ (step T v s x).events ≠ [] → F (step T v s x).state.records

theorem moments_cons (s : State v) (x : Input v) (xs : List (Input v)) :
    (run T v s (x :: xs)).2.map Result.moment =
      (step T v s x).moment :: (run T v (step T v s x).state xs).2.map Result.moment := rfl

/-- From a state where the trigger waits with a deadline at most `t0 + within` and the time is at most that, no step of a
run whose steps keep the response comes past `t0 + within` before one answers the trigger. -/
theorem late_false (tr : v.event.den0) (hG : G tr) (t0 : Int) : (xs : List (Input v)) → (s : State v) →
    Step.EachStep T (resp.Keeps T F G) s xs → F s.records → ∀ d, resp.deadlineAt s.records tr = some d →
    d ≤ t0 + (resp.withinNat : Int) → s.now ≤ t0 + (resp.withinNat : Int) →
    resp.late tr t0 ((run T v s xs).2.map Result.moment) = false
  | [], _, _, _, _, _, _, _ => rfl
  | x :: xs, s, ⟨hk, hks⟩, hF, d, hd, hdt, hst => by
    rw [moments_cons]
    have htime : (step T v s x).state.now ≤ t0 + (resp.withinNat : Int) := by
      rcases hk.clock hF tr d hG hd with h | h <;> omega
    simp only [ResponseV.late, Result.moment, Bool.or_eq_false_iff]
    refine ⟨by simp; omega, ?_⟩
    cases ha : resp.answers tr (step T v s x).moment with
    | true => simp [Result.moment] at ha ⊢; simp [ha]
    | false =>
      obtain ⟨d', hd', hle⟩ := hk.waits hF tr d hG hd ha
      have := late_false tr hG t0 xs _ hks (hk.fits (.inl hF)) d' hd' (by omega) htime
      simp [Result.moment] at ha ⊢; simp [this]

/-- A run whose every step keeps the response does not violate it. -/
theorem not_violated : (xs : List (Input v)) → (s : State v) → Step.EachStep T (resp.Keeps T F G) s xs →
    ¬ resp.Violated ((run T v s xs).2.map Result.moment)
  | [], _, _ => by rw [← resp.violated_iff]; simp [run, ResponseV.violated]
  | x :: xs, s, ⟨hk, hks⟩ => by
    rw [← resp.violated_iff, moments_cons]
    simp only [ResponseV.violated, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      not_or, not_exists, not_and]
    refine ⟨fun ev hev ⟨hop, han⟩ => ?_, by rw [resp.violated_iff]; exact not_violated xs _ hks⟩
    obtain ⟨hG, hop'⟩ := hk.opens ev hev
    obtain ⟨d, hd, hle⟩ := hop' hop han
    have hF := hk.fits (.inr (List.ne_nil_of_mem hev))
    have := late_false T resp F G ev hG (step T v s x).state.now xs _ hks hF d hd hle (by omega)
    simp [Result.moment, this]

end

/-- Whether the run of `xs` from `s` violates the response. -/
def ResponseV.violatedBy {v : ServiceV} (T : List TypeDecl) (resp : ResponseV v.records v.event) (s : State v)
    (xs : List (Input v)) : Bool :=
  resp.violated ((run T v s xs).2.map Result.moment)

end Tazuna.Ir
