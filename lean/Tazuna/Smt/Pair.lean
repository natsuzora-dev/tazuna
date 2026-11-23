import Tazuna.Smt.State

/-!
Step-order pairs: two steps that can be pending together, which no line orders, encoded in both orders from one state.
The pairs so far are two automations that react to the same event. The encodings carry no proof; prove replays each
answer that it reports in the semantics.
-/

namespace Tazuna.Smt

open Tazuna.Data Tazuna.Ir Tazuna.Service

/--
Two automations that react to the same event. Both reactions read the records before either command runs, since the
internal queue takes work before commands; no line orders the two commands, which the queue may take in either order.
-/
structure Pair where
  first : Automation
  second : Automation

/-- The pairs of automations of `st` that react to the same event, each pair once, in definition order. -/
def pairsOf (st : Service) : List Pair :=
  st.automations.zipIdx.flatMap fun (a, i) =>
    (st.automations.drop (i + 1)).filterMap fun b => if a.receives == b.receives then some { first := a, second := b } else none

/--
The react body of an automation with each createKey replaced by the field `k<i>` of the argument `key`, in written
order, and the entities of those keys. A pair's two orders take the same created keys, as ChoiceDependent renames
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

/-- An automation's reaction to the payload `payload`: whether it sends its command, the command's input, and the facts. -/
structure Reaction where
  fires : Term
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
    [Term.isStr k, .not (keyIn (.strOf k) (pre.slotsOf e))]
  let base : SEnv := { records := pre, args := fun
    | .payload => some payload
    | .now => some (.scalar (.mkInt now))
    | .key => some (.json keys)
    | _ => none }
  let binds := conditionsOf p.automationBinding
  let bindTerms ← binds.mapM fun b => do
    let (v, e) ← seval base [] b.body
    pure (b.name, v, Term.and (.not e) (.not v.nullish))
  let env := { base with args := fun x => if x == .bound then some (.obj (bindTerms.map fun (n, v, _) => (n, v)))
                                          else base.args x }
  let guards ← (conditionsOf p.automationGuard).mapM fun c => do
    let (v, e) ← seval env [] c.body
    pure (Term.and (.not e) v.truthy)
  let (input, err) ← seval env [] body
  let .obj fields := input | throw "a react that returns no object literal"
  let scalars := fields.map fun (f, v) => (f, v.scalarOf)
  let input := scalars.map fun (f, (t, _)) => (f, t)
  let props := propertiesWith ((st.schemaOf (.input a.sends.ref)).getD (.obj []))
  let fits := props.map fun pr => fieldHolds ((input.lookup pr.1).getD undefT) pr
  pure { fires := conj (bindTerms.map (·.2.2) ++ guards ++ [.not err] ++ scalars.map (.not ·.2.2)),
         input, valid := conj (fits.map (·.term)),
         facts := { vars := made.zipIdx.map fun (_, i) => (s!"{names}.k{i}", Ty.val), asserts := fresh,
                    -- A fresh key may equal the key of a deleted record, which no created key does.
                    exact := fits.all (·.exact) && made.isEmpty, complete := fits.all (·.complete) } }

/-- That two symbolic records hold the same records: each live slot of one has a live slot of the other equal to it. -/
def SRecords.same (a b : SRecords) : Term :=
  let sameSlot (x y : Slot) := conj ([y.live, .eq x.key y.key] ++ x.fields.map fun (f, t) => .eq t ((y.fields.lookup f).getD undefT))
  let within (a b : SRecords) := conj (a.keyed.flatMap fun (e, slots) =>
    slots.map fun x => .or (.not x.live) (disj ((b.slotsOf e).map (sameSlot x))))
  conj [within a b, within b a, conj (a.singles.flatMap fun (e, fields) =>
    fields.map fun (f, t) => .eq t ((((b.singles.lookup e).getD []).lookup f).getD undefT))]

/-- A pair's symbolic orders: the records and each command's acceptance after the first then second, and after the
second then first. -/
structure Orders where
  facts : Facts
  /-- That both automations send their commands, and that no step leaves the bounds or the encoding. -/
  within : Term
  gap : Term
  differ : Term
  payload : List (String × Term)
  first : Reaction
  second : Reaction

def ordersOf (st : Service) (p : Program) (pre : SRecords) (used : List (String × List Term)) (now : Term)
    (pair : Pair) : Except String Orders := do
  for a in [pair.first, pair.second] do
    if !a.sends.isOwn st.service then throw s!"{a.name} sends a request to another service, whose order prove does not compare yet"
  let fc := pair.first.sends.ref.name
  let sc := pair.second.sends.ref.name
  let props := propertiesWith ((st.schemaOf (.payload pair.first.receives)).getD (.obj []))
  let terms := props.map fun pr => (pr.1, propertyVar s!"pay.{pr.1}" pr)
  let payload := terms.map fun (f, t, _) => (f, t)
  let holds := props.map fun pr => fieldHolds ((payload.lookup pr.1).getD undefT) pr
  let payloadFacts : Facts := { vars := terms.flatMap (·.2.2), asserts := holds.map (·.term),
                                exact := holds.all (·.exact), complete := holds.all (·.complete) }
  let a ← reactionOf st p pre now (.json payload) pair.first "ra"
  let b ← reactionOf st p pre now (.json payload) pair.second "rb"
  let accepted (r : Reaction) (step : Step) : Term := .and r.valid step.accepted
  let after (r : Reaction) (step : Step) (records : SRecords) (used : List (String × List Term)) :
      SRecords × List (String × List Term) :=
    (.ite (accepted r step) step.post records,
     used.map fun (e, us) => (e, (us.zip ((step.used.lookup e).getD [])).map fun (u, w) => .ite (accepted r step) w u))
  -- An automation sends its own service's command as that service (State.callerOf).
  let own := callerTerms (.service st.service)
  let a1 ← stepWith st p pre used fc a.input own now "o1a."
  let (r1, u1) := after a a1 pre used
  let b1 ← stepWith st p r1 u1 sc b.input own now "o1b."
  let (r12, _) := after b b1 r1 u1
  let b2 ← stepWith st p pre used sc b.input own now "o2b."
  let (r2, u2) := after b b2 pre used
  let a2 ← stepWith st p r2 u2 fc a.input own now "o2a."
  let (r21, _) := after a a2 r2 u2
  let steps := [a1, b1, b2, a2]
  pure { facts := payloadFacts ++ a.facts ++ b.facts ++ steps.foldl (· ++ ·.facts) {},
         within := conj ([a.fires, b.fires] ++ steps.map (.not ·.beyond)),
         gap := disj (steps.map (·.gap)),
         differ := disj [.not (r12.same r21), .not (.eq (accepted a a1) (accepted a a2)),
           .not (.eq (accepted b b1) (accepted b b2))],
         payload, first := a, second := b }

end Tazuna.Smt
