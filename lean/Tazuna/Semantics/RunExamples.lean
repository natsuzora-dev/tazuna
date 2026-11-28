import Tazuna.Semantics.StepExamples
import Tazuna.Semantics.Response
import Tazuna.Semantics.Valid
import Tazuna.Semantics.GenTarget

/-! Examples of what runs mean beyond one step, on hand-written steps and on runs of the example service `sum`:
responses, the timely-clock assumption, and the behavior targets. -/

namespace Tazuna.Ir.RunExamples

open StepExamples

/-- No deadline: what a run violates reads none. -/
def noDeadline : Fun (Ty.fn [Ty.int, Ty.int] (Ty.option (.point .ms))) :=
  .closed (.lam (.ctor (vs := [[.point .ms], []]) ⟨1, by simp⟩ .nil))

/-- After an event `a`, an event `b` within 10 ms. -/
def resp (a b : Int) : ResponseV .int .int :=
  { name := "r", after := .closed (.lam (.bin (.eq rfl) (.var .here) (.int a))),
    then_ := .closed (.lam (.bin (.eq rfl) (.var (.there .here)) (.int b))), within := 10,
    deadline := noDeadline }

/-- After any event, the event one above it within 10 ms: `then` ties the answer to its trigger. -/
def respNext : ResponseV .int .int :=
  { name := "r", after := .closed (.lam (.bin (.eq rfl) (.var .here) (.var .here))),
    then_ := .closed (.lam (.bin (.eq rfl) (.var (.there .here)) (.bin .add (.var .here) (.int 1)))), within := 10,
    deadline := noDeadline }

def at_ (t : Int) (evs : List Int) : Moment .int := ⟨t, evs⟩

-- An answer in the opening step counts, whatever the order inside the step.
#guard !(resp 1 2).violated [at_ 0 [2, 1], at_ 50 []]
-- The deadline itself is in time; one ms past it is not.
#guard !(resp 1 2).violated [at_ 0 [1], at_ 10 []]
#guard (resp 1 2).violated [at_ 0 [1], at_ 11 []]
-- An answer before the deadline closes it; one in the step that comes late does not save it.
#guard !(resp 1 2).violated [at_ 0 [1], at_ 5 [2], at_ 20 []]
#guard (resp 1 2).violated [at_ 0 [1], at_ 20 [2]]
-- A run that ends before the deadline does not violate.
#guard !(resp 1 2).violated [at_ 0 [1], at_ 3 []]
-- A later opening is judged on its own.
#guard (resp 1 2).violated [at_ 0 [1], at_ 5 [2], at_ 6 [1], at_ 17 []]
-- Each trigger waits for its own answer: 2 answers 1 but nothing answers 2, and then the run comes late for 2.
#guard !respNext.violated [at_ 0 [1], at_ 5 [2], at_ 15 [3]]
#guard respNext.violated [at_ 0 [1], at_ 5 [2], at_ 16 []]
-- Two triggers in one step make two deadlines; an answer to one does not close the other.
#guard respNext.violated [at_ 0 [1, 5], at_ 5 [2], at_ 11 []]
#guard !respNext.violated [at_ 0 [1, 5], at_ 5 [2, 6], at_ 11 []]

-- On `sum`: `add 5` applies 5 at time 0; a clock line at 11 is past the deadline of "after 5, 99 within 10", one at 10
-- is not.
#guard (resp 5 99).violatedBy prelude s0 [cmd 1 5, .clock 11]
#guard !(resp 5 99).violatedBy prelude s0 [cmd 1 5, .clock 10]
-- After `add 5` and `add 1`, the machine waits for its timer due at 10: a clock line at 10 is timely, one at 11 is not.
#guard Step.timely (after s0 [cmd 1 5, cmd 1 1]) 10
#guard !Step.timely (after s0 [cmd 1 5, cmd 1 1]) 11

/-- `sum`'s literal rule names: `add` names `small`; `total` names none. -/
def rules : RuleNames := fun n => if n == "add" then [some "small"] else []

def targetTexts : List GenTarget := targets prelude svc rules

-- Per command its outcomes (String rejections have no constructor), per query its own, an event of a type with no
-- constructors, and the request the machine can send.
#guard targetTexts == [.accepted "add", .rejected "add" none, .invalid "add" (some "callers"),
  .invalid "add" (some "small"), .answered "total", .invalid "total" (some "callers"), .event none,
  .request "mail" "ping"]

/-- Whether some target aims at each class the last input's step shows. -/
def covered (xs : List (Input svc)) (x : Input svc) : Bool :=
  (classes prelude svc x (step prelude svc (after s0 xs) x)).all fun c => targetTexts.any (·.covers rules c)

#guard (classes prelude svc (cmd 1 500) (step prelude svc s0 (cmd 1 500))) == [.invalid "add" "small"]
#guard covered [] (cmd 2 5) && covered [] (cmd 1 0) && covered [] (cmd 1 5)
-- The clock line at the deadline sends `ping`.
#guard (classes prelude svc (.clock 10) (step prelude svc (after s0 [cmd 1 5, cmd 1 1]) (.clock 10))) ==
  [.request "mail" "ping"]

end Tazuna.Ir.RunExamples
