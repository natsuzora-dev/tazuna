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

/-- A request to an external's command or query; the answer becomes events. The external is the one that lists the
command or query, which the step finds. -/
structure RequestV (e : Ty) where
  name : String
  input : Ty
  output : Ty
  /-- A command's rejection type; a query has none. -/
  rejection : Option Ty
  value : input.den0
  /-- The rules an answer keeps: a query's `ensures` at this input; a command's answer keeps none. -/
  holds : (answerTy output rejection).den0 → Ty.rules.den0
  onAnswer : (Ty.fn [answerTy output rejection] (.list e)).den0

/-- A command; the service that lists it owns it. -/
structure CommandV (r e c : Ty) where
  name : String
  input : Ty
  rejection : Ty
  callers : List c.den0
  accepts : (Ty.fn [input] Ty.rules).den0
  decide : (Ty.fn [Ty.ctx r input c] (Ty.result (.list e) rejection)).den0
  ensures : (Ty.fn [Ty.ctx r input c, r] Ty.rules).den0

/-- A query; the service that lists it owns it. -/
structure QueryV (r c : Ty) where
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
  on : (Ty.fn [Ty.machineCtx key state r, e] (Ty.next state)).den0
  after : (Ty.fn [Ty.machineCtx key state r] (Ty.option (Ty.timer state))).den0
  effect : key.den0 → state.den0 → r.den0 → Int → Option (EffectV e)
  invariants : (Ty.fn [Ty.machineCtx key state r] Ty.rules).den0

structure ReactionV (r e : Ty) where
  name : String
  react : e.den0 → r.den0 → Int → List (EffectV e)

/-- A declaration, for the service or external that owns it: the handle, with the types that make it that handle. -/
inductive DeclaredV where
  | command (r e c : Ty) (x : CommandV r e c)
  | query (r c : Ty) (x : QueryV r c)
  | externalCommand (name : String) (input output rejection : Ty)
  | externalQuery (name : String) (input output : Ty) (holds : (Ty.fn [input, output] Ty.rules).den0)
  | source (name : String) (event : Ty)

/-- An external: the commands, queries and sources it declares. -/
structure ExternalV where
  name : String
  declares : List DeclaredV

/-- Another service's or an external's source, whose events this service receives as its own. -/
structure SubscriptionV (e : Ty) where
  /-- The service or external that lists the source with this name and event type, which `spec` finds; empty when
  none does. -/
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

/-- One step of a scenario, typed by its service's records, event and caller. -/
inductive StepV (r e c : Ty) where
  /-- The command, then the steps `next` gives for the counter its new ids came from (`Ctx.fresh`). -/
  | command (x : CommandV r e c) (caller : c.den0) (input : x.input.den0) (next : Nat → List (StepV r e c))
  | query (x : QueryV r c) (caller : c.den0) (input : x.input.den0)
  /-- Time moves on by `ms`: a clock line, which fires the timers due. -/
  | wait (ms : Int)
  /-- The answer to the one pending request that `sender` sent to the external command or query `name` of these
  types (a query has no rejection type). -/
  | answer (name : String) (input output : Ty) (rejection : Option Ty) (sender : Sender) (value : WireVal)
  /-- An event of the source `name`, whose event type is the value's. -/
  | event (name : String) (value : WireVal)

/-- A scenario: steps from its service's initial records at time 0. -/
structure ScenarioV (r e c : Ty) where
  name : String
  steps : List (StepV r e c)

structure ServiceV where
  name : String
  records : Ty
  event : Ty
  caller : Ty
  init : records.den0
  apply : (Ty.fn [records, event] records).den0
  subscribes : List (SubscriptionV event)
  /-- What it declares, as written. -/
  declares : List DeclaredV
  /-- The commands it lists that are typed for it. -/
  commands : List (CommandV records event caller)
  queries : List (QueryV records caller)
  /-- The sources it lists: names and event types. -/
  sources : List (String × Ty)
  machines : List (MachineV records event)
  reactions : List (ReactionV records event)
  invariants : (Ty.fn [records] Ty.rules).den0
  responses : List (ResponseV event)
  bounds : BoundsV records
  scenarios : List (ScenarioV records event caller)
  /-- The commands and queries the spec's externals list, each with its external, which `spec` fills in: an effect
  may request only these. -/
  declared : List (String × DeclaredV)

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
      | .command, [r, e, c, i, j] => CommandOf r e c i j
      | .query, [r, c, i, o] => QueryOf r c i o
      | .machine, [r, e] => MachineV r e
      | .reaction, [r, e] => ReactionV r e
      | .external, _ => ExternalV
      | .externalCommand, [_, _, _] => String
      | .externalQuery, [i, o] => String × (Ty.fn [i, o] Ty.rules).den0
      | .source, [_] => String
      | .declared, _ => DeclaredV
      | .effect, [e] => EffectV e
      | .subscription, [e] => SubscriptionV e
      | .bounds, [r] => BoundsV r
      | .create, [r] => CreateV r
      | .response, [e] => ResponseV e
      | .scenario, [r, e, c] => ScenarioV r e c
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

theorem Ty.up_down (t : Ty) (h : t.isData = true) (x : (Ty.semWith Dsl.val t).1) : Ty.up t h (Ty.down t h x) = x := by
  simp [Ty.up, Ty.down]

theorem Ty.down_up (t : Ty) (h : t.isData = true) (x : t.den0) : Ty.down t h (Ty.up t h x) = x := by
  simp [Ty.up, Ty.down]

/-! How `up` meets the shapes of data: it moves into functions, pairs, lists and equality. -/

theorem cast_fn {A A' B B' : Type} (eA : A = A') (eB : B = B') (e : (A → B) = (A' → B')) (f : A → B) (x : A) :
    cast e f (cast eA x) = cast eB (f x) := by subst eA; subst eB; rfl

theorem cast_prod {A A' B B' : Type} (eA : A = A') (eB : B = B') (e : (A × B) = (A' × B')) (a : A) (b : B) :
    cast e (a, b) = (cast eA a, cast eB b) := by subst eA; subst eB; rfl

theorem cast_sumL {A A' B B' : Type} (eA : A = A') (eB : B = B') (e : (A ⊕ B) = (A' ⊕ B')) (a : A) :
    cast e (Sum.inl a : A ⊕ B) = Sum.inl (cast eA a) := by subst eA; subst eB; rfl

theorem cast_list {A A' : Type} (eA : A = A') (e : List A = List A') (xs : List A) :
    cast e xs = xs.map (cast eA) := by
  subst eA
  have : (cast (rfl : A = A) : A → A) = id := funext fun _ => rfl
  simp [this]

theorem cast_sem (S S' : Sem) (e : S = S') (a b : S.1) :
    S'.2 (cast (congrArg Sigma.fst e) a) (cast (congrArg Sigma.fst e) b) = S.2 a b := by subst e; rfl

theorem Ty.up_fn (ps : List Ty) (r : Ty) (h : (Ty.fn ps r).isData = true) (hps : (Ty.tuple ps).isData = true)
    (hr : r.isData = true) (f : (Ty.fn ps r).den0) (xs : (Ty.tuple ps).den0) :
    Ty.up (.fn ps r) h f (Ty.up (.tuple ps) hps xs) = Ty.up r hr (f xs) := by
  unfold Ty.up; exact cast_fn _ _ _ f xs

theorem Ty.up_tuple (t : Ty) (ts : List Ty) (h : (Ty.tuple (t :: ts)).isData = true) (ht : t.isData = true)
    (hts : (Ty.tuple ts).isData = true) (x : (Ty.tuple (t :: ts)).den0) :
    Ty.up (.tuple (t :: ts)) h x = (Ty.up t ht x.1, Ty.up (.tuple ts) hts x.2) := by
  obtain ⟨a, b⟩ := x
  unfold Ty.up; exact cast_prod _ _ _ a b

theorem Ty.up_inl (k : Nat) (a : List Ty) (fs : List Ty) (vs : List (List Ty)) (h : (Ty.adt k a (fs :: vs)).isData = true)
    (hfs : (Ty.tuple fs).isData = true) (x : (Ty.tuple fs).den0) :
    Ty.up (.adt k a (fs :: vs)) h (.inl x) = .inl (Ty.up (.tuple fs) hfs x) := by
  have hvs : Ty.isDatass vs = true := by simp_all [Ty.isData, Ty.isDatass]
  unfold Ty.up
  exact cast_sumL _ (congrArg Sigma.fst (Ty.semAltsWith_data Dsl.val_fresh vs hvs)).symm _ x

theorem Ty.up_int (h : Ty.int.isData = true) (n : Ty.int.den0) : Ty.up .int h n = n := rfl
theorem Ty.up_fresh (h : (Ty.dsl .fresh []).isData = true) (n : (Ty.dsl .fresh []).den0) : Ty.up (.dsl .fresh []) h n = n := rfl
theorem Ty.up_nil (h : (Ty.tuple []).isData = true) (x : (Ty.tuple []).den0) : Ty.up (.tuple []) h x = () := rfl

theorem Ty.up_list (t : Ty) (h : (Ty.list t).isData = true) (ht : t.isData = true) (xs : (Ty.list t).den0) :
    Ty.up (.list t) h xs = xs.map (Ty.up t ht) := by
  unfold Ty.up; exact cast_list _ _ xs

theorem Ty.deq_up (t : Ty) (h : t.isData = true) (a b : t.den0) :
    (Ty.semWith Dsl.val t).2 (Ty.up t h a) (Ty.up t h b) = (Ty.semWith Dsl.base t).2 a b := by
  unfold Ty.up; exact cast_sem _ _ (Ty.semWith_data Dsl.val_fresh t h).symm a b

end Tazuna.Ir
