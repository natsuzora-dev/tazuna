import Tazuna.Semantics.Data

/-! What the structure types mean: the values the `tazuna` built-ins build from a spec's definitions. A structure value
holds data (`Ty.den0`) and the types of that data, so a list of commands can hold commands of different input types. -/

namespace Tazuna.Ir

/-- A value with its type, as it crosses the wire. -/
abbrev WireVal := (t : Ty) × t.den0

/-- What started an effect: an instance of a machine, by the machine's name and the instance's key, or a reaction. -/
inductive Sender where
  | machine (name : String) (key : WireVal)
  | reaction (name : String)

/-- What an answer to a request to an external carries: the output or the rejection for a command, which has a
rejection type, and the output for a query, which has none. -/
def answerTy (output : Ty) : Option Ty → Ty
  | some rejection => Ty.result output rejection
  | none => output

/-- A request to an external's command or query; the answer becomes events. -/
structure RequestV (e : Ty) where
  external : String
  name : String
  input : Ty
  output : Ty
  /-- A command's rejection type; a query has none. -/
  rejection : Option Ty
  value : input.den0
  /-- The rules an answer keeps: a query's `ensures` at this input; a command's answer keeps none. -/
  holds : (answerTy output rejection).den0 → Ty.rules.den0
  onAnswer : (Ty.fn [answerTy output rejection] (.list e)).den0

/-- A command of the service `service`. -/
structure CommandV (r e c : Ty) where
  service : String
  name : String
  input : Ty
  rejection : Ty
  callers : List c.den0
  accepts : (Ty.fn [input] Ty.rules).den0
  decide : (Ty.fn [Ty.ctx r input c] (Ty.result (.list e) rejection)).den0
  ensures : (Ty.fn [Ty.ctx r input c, r] Ty.rules).den0

/-- A query of the service `service`. -/
structure QueryV (r c : Ty) where
  service : String
  name : String
  input : Ty
  output : Ty
  callers : List c.den0
  accepts : (Ty.fn [input] Ty.rules).den0
  resolve : (Ty.fn [Ty.ctx r input c] output).den0

/-- A command whose input and rejection types are `i` and `j`: the value of `Command(records, event, caller, input,
rejection)`, so a handle's types are the command's. -/
abbrev CommandOf (r e c i j : Ty) := { x : CommandV r e c // x.input = i ∧ x.rejection = j }

abbrev QueryOf (r c i o : Ty) := { x : QueryV r c // x.input = i ∧ x.output = o }

/-- A command or query, as a service lists it. -/
inductive DefinitionV (r e c : Ty) where
  | command (x : CommandV r e c)
  | query (x : QueryV r c)

/-- What a machine or reaction starts: a request to an external, or a command or query of its own service run inside
the same step. An own command's answer is `Ok(Nil)` once its events are applied, or its rejection. -/
inductive EffectV (e : Ty) where
  | request (x : RequestV e)
  | command (r c : Ty) (x : CommandV r e c) (caller : c.den0) (input : x.input.den0)
      (onAnswer : (Ty.fn [Ty.result Ty.nil x.rejection] (.list e)).den0)
  | query (r c : Ty) (x : QueryV r c) (caller : c.den0) (input : x.input.den0)
      (onAnswer : (Ty.fn [x.output] (.list e)).den0)

structure MachineV (r e : Ty) where
  name : String
  key : Ty
  state : Ty
  instances : (Ty.fn [r] (.bag key)).den0
  initial : state.den0
  on : (Ty.fn [key, state, e, r, .int] (Ty.next state)).den0
  after : (Ty.fn [key, state, r, .int] (Ty.option (Ty.timer state))).den0
  effect : key.den0 → state.den0 → r.den0 → Int → Option (EffectV e)
  invariants : (Ty.fn [key, state, r] Ty.rules).den0

structure ReactionV (r e : Ty) where
  name : String
  react : e.den0 → r.den0 → Int → List (EffectV e)

/-- What an external declares: a command (with its rejection type), a query (with what its answers ensure) or an
event. The wire name is `external.name`. -/
inductive DeclaredV where
  | command (external name : String) (input output rejection : Ty)
  | query (external name : String) (input output : Ty) (holds : (Ty.fn [input, output] Ty.rules).den0)
  | event (external name : String) (ty : Ty)

structure ExternalV where
  name : String
  declared : List DeclaredV

/-- Another service's or an external's event, received as an event of this service. -/
structure SubscriptionV (e : Ty) where
  source : String
  name : String
  event : Ty
  wrap : (Ty.fn [event] e).den0

/-- A bound on the keys created in the table `table` reads from the records. -/
structure CreateV (r : Ty) where
  key : Ty
  value : Ty
  table : (Ty.fn [r] (.table key value)).den0
  atMost : Int

structure BoundsV (r : Ty) where
  creates : List (CreateV r)
  items : Int
  cascade : Int
  steps : Int

structure ResponseV (e : Ty) where
  name : String
  after : (Ty.fn [e] Ty.bool).den0
  then_ : (Ty.fn [e] Ty.bool).den0
  within : Int

structure ServiceV where
  name : String
  records : Ty
  event : Ty
  caller : Ty
  init : records.den0
  apply : (Ty.fn [records, event] records).den0
  subscribes : List (SubscriptionV event)
  commands : List (CommandV records event caller)
  queries : List (QueryV records caller)
  machines : List (MachineV records event)
  reactions : List (ReactionV records event)
  invariants : (Ty.fn [records] Ty.rules).den0
  responses : List (ResponseV event)
  bounds : BoundsV records
  /-- What the spec's externals declare, which `spec` fills in: an effect may request only a declared command or
  query. -/
  declared : List DeclaredV

/-- One step of a scenario, typed by its service's records, event and caller. -/
inductive StepV (r e c : Ty) where
  | command (x : CommandV r e c) (caller : c.den0) (input : x.input.den0)
  | query (x : QueryV r c) (caller : c.den0) (input : x.input.den0)
  /-- Time moves on by `ms`: a clock line, which fires the timers due. -/
  | wait (ms : Int)
  /-- The answer to the one pending request to `external.name` that `sender` sent. -/
  | answer (external name : String) (sender : Sender) (value : WireVal)
  | event (source name : String) (value : WireVal)

/-- A scenario of the service `service`: steps from the initial records at time 0. -/
structure ScenarioV where
  service : String
  name : String
  records : Ty
  event : Ty
  caller : Ty
  steps : List (StepV records event caller)

structure SpecV where
  services : List ServiceV
  externals : List ExternalV
  scenarios : List ScenarioV

/-- What each structure type means. Structure values have no `==`. -/
def Dsl.val : Dsl → List Ty → Sem
  | .fresh, _ => Dsl.base .fresh []
  | k, args =>
    let carrier : Type := match k, args with
      | .spec, _ => SpecV
      | .service, _ => ServiceV
      | .command, [r, e, c, i, j] => CommandOf r e c i j
      | .query, [r, c, i, o] => QueryOf r c i o
      | .definition, [r, e, c] => DefinitionV r e c
      | .machine, [r, e] => MachineV r e
      | .reaction, [r, e] => ReactionV r e
      | .external, _ => ExternalV
      | .externalCommand, [_, _, _] => String × String
      | .externalQuery, [i, o] => String × String × (Ty.fn [i, o] Ty.rules).den0
      | .externalEvent, [_] => String × String
      | .declared, _ => DeclaredV
      | .effect, [e] => EffectV e
      | .subscription, [e] => SubscriptionV e
      | .bounds, [r] => BoundsV r
      | .create, [r] => CreateV r
      | .response, [e] => ResponseV e
      | .scenario, _ => ScenarioV
      | .step, [r, e, c] => StepV r e c
      | .sender, _ => Sender
      | _, _ => Unit
    ⟨carrier, fun _ _ => false⟩

theorem Dsl.val_fresh (a : List Ty) : Dsl.val .fresh a = Dsl.base .fresh a := rfl

/-- A data value read at the structure level: the same value, since data means the same at both. -/
def Ty.up (t : Ty) (h : t.isData = true) (x : t.den0) : (Ty.semWith Dsl.val t).1 :=
  cast (congrArg Sigma.fst (Ty.semWith_data Dsl.val_fresh t h)).symm x

def Ty.down (t : Ty) (h : t.isData = true) (x : (Ty.semWith Dsl.val t).1) : t.den0 :=
  cast (congrArg Sigma.fst (Ty.semWith_data Dsl.val_fresh t h)) x

end Tazuna.Ir
