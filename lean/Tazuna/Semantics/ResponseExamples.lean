import Tazuna.Semantics.StepExamples
import Tazuna.Semantics.Response
import Tazuna.Semantics.Valid

/-! Examples of responses on hand-written steps and on runs of the example service `sum`, and of the timely-clock
assumption. -/

namespace Tazuna.Ir.ResponseExamples

open StepExamples

/-- After an event `a`, an event `b` within 10 ms. -/
def resp (a b : Int) : ResponseV .int :=
  { name := "r", after := fun (x, ()) => Ty.ofBool ((show Int from x) == a),
    then_ := fun (x, ()) => Ty.ofBool ((show Int from x) == b), within := 10 }

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

-- On `sum`: `add 5` applies 5 at time 0; a clock line at 11 is past the deadline of "after 5, 99 within 10", one at 10
-- is not.
#guard (resp 5 99).violatedBy prelude s0 [cmd 1 5, .clock 11]
#guard !(resp 5 99).violatedBy prelude s0 [cmd 1 5, .clock 10]
-- After `add 5` and `add 1`, the machine waits for its timer due at 10: a clock line at 10 is timely, one at 11 is not.
#guard Step.timely (after s0 [cmd 1 5, cmd 1 1]) 10
#guard !Step.timely (after s0 [cmd 1 5, cmd 1 1]) 11

end Tazuna.Ir.ResponseExamples
