import Tazuna.Semantics.Data

/-! What the structure types mean: the values the `tazuna` built-ins build from a spec's definitions. A structure value
holds data (`Ty.den0`) and the types of that data, so a list of commands can hold commands of different input types. -/

namespace Tazuna.Ir

/-- A request to an external command; the answer, an output or a rejection, becomes events. -/
structure EffectV (e : Ty) where
  external : String
  command : String
  input : Ty
  output : Ty
  rejection : Ty
  value : input.den0
  onAnswer : (Ty.fn [Ty.result output rejection] (.list e)).den0

structure CommandV (r e c : Ty) where
  name : String
  input : Ty
  rejection : Ty
  callers : List c.den0
  accepts : (Ty.fn [input] Ty.rules).den0
  decide : (Ty.fn [Ty.ctx r input c] (Ty.result (.list e) rejection)).den0
  ensures : (Ty.fn [Ty.ctx r input c, r] Ty.rules).den0

structure QueryV (r c : Ty) where
  name : String
  input : Ty
  output : Ty
  callers : List c.den0
  accepts : (Ty.fn [input] Ty.rules).den0
  resolve : (Ty.fn [Ty.ctx r input c] output).den0

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

structure SpecV where
  services : List ServiceV
  externals : List ExternalV

/-- What each structure type means. Structure values have no `==`. -/
def Dsl.val : Dsl → List Ty → Sem
  | .fresh, _ => Dsl.base .fresh []
  | k, args =>
    let carrier : Type := match k, args with
      | .spec, _ => SpecV
      | .service, _ => ServiceV
      | .command, [r, e, c] => CommandV r e c
      | .query, [r, c] => QueryV r c
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
      | _, _ => Unit
    ⟨carrier, fun _ _ => false⟩

theorem Dsl.val_fresh (a : List Ty) : Dsl.val .fresh a = Dsl.base .fresh a := rfl

/-- A data value read at the structure level: the same value, since data means the same at both. -/
def Ty.up (t : Ty) (h : t.isData = true) (x : t.den0) : (Ty.semWith Dsl.val t).1 :=
  cast (congrArg Sigma.fst (Ty.semWith_data Dsl.val_fresh t h)).symm x

def Ty.down (t : Ty) (h : t.isData = true) (x : (Ty.semWith Dsl.val t).1) : t.den0 :=
  cast (congrArg Sigma.fst (Ty.semWith_data Dsl.val_fresh t h)) x

end Tazuna.Ir
