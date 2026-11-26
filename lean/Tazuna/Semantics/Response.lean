import Tazuna.Semantics.Step

/-! What a bounded response means: "after each event `trigger` satisfying `after`, an event satisfying
`then(trigger, event)` within `within` ms". A run violates it when some step applies an `after` event and a later step
comes past the deadline with no step from the first one up to it applying an event that `then` ties to that trigger.
Each trigger is judged on its own, so two `after` events in one step make two deadlines. A response is judged per
step: a `then` event in the same step as its trigger counts, whatever their order inside the step, since that order is
the semantics' canonical one and a verdict resting on it would rest on an order the spec does not write. A run that
ends before the deadline does not violate, so every violation has a finite witness and a bounded search over runs
finds every one within its bound. Time is the state's after each step: a clock line's events carry the clock line's
time. -/

namespace Tazuna.Ir

/-- What a response reads of one step of a run: its time, and the events it applied. -/
structure Moment (e : Ty) where
  time : Int
  events : List e.den0

/-- A step's moment: the time after it and the events it applied. -/
def Result.moment {v : ServiceV} (r : Result v) : Moment v.event := ⟨r.state.now, r.events⟩

namespace ResponseV

variable {e : Ty} (resp : ResponseV e)

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

end ResponseV

/-- Whether the run of `xs` from `s` violates the response. -/
def ResponseV.violatedBy {v : ServiceV} (T : List TypeDecl) (resp : ResponseV v.event) (s : State v)
    (xs : List (Input v)) : Bool :=
  resp.violated ((run T v s xs).2.map Result.moment)

end Tazuna.Ir
