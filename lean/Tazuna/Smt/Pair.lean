import Tazuna.Smt.State

/-!
An automation's reaction to an event, which decides the command it sends, and the sameness of two symbolic records, which
two orders compare. The encodings carry no proof; prove replays each answer that it reports in the semantics.
-/

namespace Tazuna.Smt

open Tazuna.Ir Tazuna.Semantics Tazuna.Semantics.Eval Tazuna.Semantics.Service

/--
The react body of an automation with each createKey replaced by the field `k<i>` of the argument `key`, in written
order, and the entities of those keys. Two orders take the same created keys, as ChoiceDependent renames
created keys before it compares.
-/
partial def withKeys : Expr → StateM (List String) Expr
  | .createKey e => do
    let made ← get
    set (made ++ [e])
    pure (.field (.arg .key) s!"k{made.length}")
  | .let x v b => do pure (.let x (← withKeys v) (← withKeys b))
  | .ite c y n => do pure (.ite (← withKeys c) (← withKeys y) (← withKeys n))
  | .and a b => do pure (.and (← withKeys a) (← withKeys b))
  | .or a b => do pure (.or (← withKeys a) (← withKeys b))
  | .coalesce a b => do pure (.coalesce (← withKeys a) (← withKeys b))
  | .not a => do pure (.not (← withKeys a))
  | .eq a b => do pure (.eq (← withKeys a) (← withKeys b))
  | .field o n => do pure (.field (← withKeys o) n)
  | .fieldOpt o n => do pure (.fieldOpt (← withKeys o) n)
  | .obj fs => do pure (.obj (← fs.mapM fun f => do pure { f with value := ← withKeys f.value }))
  | .arr vs => do pure (.arr (← vs.mapM withKeys))
  | e => pure e

/--
An automation's reaction to the payload `payload`: whether it sends its command or halts (StepEnd), the command's input,
and the facts.
-/
structure Reaction where
  /-- Accepted when every binds value is present, every guard holds and react returns; halted when one of them throws. -/
  ending : StepEnd
  /-- That react returns a field that the encoding holds as no scalar. -/
  gap : Term
  input : List (String × Term)
  /-- That the input fits the command's input schema, which the command otherwise rejects as invalid input. -/
  valid : Term
  facts : Facts

def reactionOf (st : Service) (p : Program) (pre : SRecords) (now : Term) (payload : SVal) (a : Automation)
    (names : String) : Except String Reaction := do
  let some react := p.react.find? (·.definition == st.ref a.name) | throw s!"no react of {a.name}"
  let conditionsOf (list : List Conditions) : List Condition :=
    ((list.find? (·.definition == st.ref a.name)).map (·.conditions)).getD []
  let (body, made) := (withKeys react.body).run []
  let keys := made.zipIdx.map fun (_, i) => (s!"k{i}", valVar s!"{names}.k{i}")
  let fresh := made.zipIdx.flatMap fun (e, i) =>
    let k := valVar s!"{names}.k{i}"
    [Term.isStr k, .not (keyIn k (pre.slotsOf e))]
  let base : SEnv := { records := pre, args := fun
    | .payload => some payload
    | .now => some (.scalar (.mkInt now))
    | .key => some (.json (SJson.ofTerms keys))
    | _ => none }
  let binds := conditionsOf p.automationBinding
  let bindTerms ← binds.mapM fun b => do
    let (v, e) ← seval base [] b.body
    pure (b.name, v, ({ name := b.name, throws := e, passes := .not v.nullish } : Check))
  let env := { base with args := fun x => if x == .bound then some (.obj (bindTerms.map fun (n, v, _) => (n, v)))
                                          else base.args x }
  let guards ← (conditionsOf p.automationGuard).mapM fun c => do
    let (v, e) ← seval env [] c.body
    pure ({ name := c.name, throws := e, passes := v.truthy } : Check)
  let (input, err) ← seval env [] body
  let .obj fields := input | throw "a react that returns no object literal"
  let scalars := fields.map fun (f, v) => (f, v.scalarOf)
  let input := scalars.map fun (f, (t, _)) => (f, t)
  let props := propertiesWith ((st.schemaOf (.input a.sends.ref)).getD (.obj []))
  let fits := props.map fun pr => fieldHolds ((input.lookup pr.1).getD undefT) pr
  -- The semantics checks the binds, then the guards, each up to the first that fails (workBody), then runs react.
  let checks := bindTerms.map (·.2.2) ++ guards
  let accepted := conj (checks.map (·.held) ++ [.not err])
  let halts := throwsFirst (checks.map (fun c => (c.throws, c.passes)) ++ [(err, tt)])
  pure { ending := { accepted, halted := { term := halts, fit := .exact } },
         gap := .and accepted (disj (scalars.map (·.2.2))),
         input, valid := conj (fits.map (·.term)),
         facts := { vars := made.zipIdx.map fun (_, i) => (s!"{names}.k{i}", Ty.val), asserts := fresh,
                    -- A fresh key may equal the key of a deleted record, which no created key does.
                    fit := (Fit.all (fits.map (·.fit))).join (.of made.isEmpty true) } }

/-- That two symbolic records hold the same records: each live slot of one has a live slot of the other equal to it. -/
def SRecords.same (a b : SRecords) : Term :=
  let sameSlot (x y : Slot) := conj ([y.live] ++ x.fields.map fun (f, t) => .eq t ((y.fields.lookup f).getD undefT))
  let within (a b : SRecords) := conj (a.keyed.flatMap fun (e, slots) =>
    slots.map fun x => .or (.not x.live) (disj ((b.slotsOf e).map (sameSlot x))))
  conj [within a b, within b a, conj (a.singles.flatMap fun (e, fields) =>
    fields.map fun (f, t) => .eq t ((((b.singles.lookup e).getD []).lookup f).getD undefT))]

end Tazuna.Smt
