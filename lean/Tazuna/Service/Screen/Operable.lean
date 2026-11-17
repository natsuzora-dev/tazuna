import Tazuna.Service.Chart.Select

namespace Tazuna.Service

open Tazuna.Data

variable {m : Type → Type}

/--
An operation that the screen instance `resource` of chart `screen` accepts. `payloads = none` accepts every payload that
matches the schema.
-/
structure Operation where
  screen : String
  resource : String
  control : String
  payloads : Option (List Value)
deriving DecidableEq, Repr, Inhabited

section Operations

variable [Monad m] (fs : Functions m)

inductive Refusal where
  | notOpen
  | covered (child : String)
  | notOffered
deriving DecidableEq, Repr, Inhabited

def Refusal.finding (st : Service) (screen control : String) (payload : Value) : Refusal → Finding
  | .notOpen => .invalidInput (.unopenedScreen (st.ref screen) control)
  | .covered child => .invalidInput (.coveredByModal (st.ref screen) control (st.ref child))
  | .notOffered => .invalidInput (.unofferedPayload (st.ref screen) control payload)

/--
The open screen instance `resource` when it accepts operations, or the refusal. As with HTML `dialog.showModal()`, a
modal opened after it blocks it; several instances of one screen are each operable.
-/
def State.accepting (s : State) (resource : String) : Except Refusal Instance :=
  go s.stack.reverse
where
  go : List String → Except Refusal Instance
    | [] => .error .notOpen
    | r :: rest =>
      match s.machine? r with
      | some i =>
        if r == resource then .ok i else
        match i.opener with
        | some o => if o.modal then .error (.covered i.chart.name) else go rest
        | none => go rest
      | none => go rest

def offeringStates (st : Service) (s : State) (top : Instance) (control : String) (payload : Value) :
    m (Except Fault (List (Instance × String × Spec.Offer))) := do
  pure ((← reachedCopies fs st s top payload).map fun reached => top.documentOrder.filterMap fun (h, n) =>
    let holder := if h == top.resource then some top else if h ∈ reached then s.machine? h else none
    holder.bind fun hi =>
      match (top.chart.state? n).bind (·.offers.lookup control) with
      | some o => if hi.isIn n then some (hi, n, o) else none
      | none => none)

/--
The offering states that no active descendant overrides. A descendant held by one map copy overrides the states of that
copy and of `top`, but not those of another copy.
-/
def innermostOffers (top : Instance) (found : List (Instance × String × Spec.Offer)) :
    List (Instance × String × Spec.Offer) :=
  let tree := top.chart.tree
  found.filter fun (h, a, _) => !found.any fun (g, b, _) =>
    b != a && tree.isDescendant b a && (g.resource == h.resource || h.resource == top.resource)

/--
The offers that apply to `control`: the innermost offering states, or else the chart's own offers. A control that
neither names is offered nothing.
-/
def appliedOffers (top : Instance) (control : String) (found : List (Instance × String × Spec.Offer)) :
    List (Instance × Option String × Spec.Offer) :=
  match innermostOffers top found, top.chart.offers.lookup control with
  | [], some o => [(top, none, o)]
  | innermost, _ => innermost.map fun (h, n, o) => (h, some n, o)

/-- The payloads that one applying offers gives a control. -/
inductive Offered where
  | any
  | listed (payloads : List Value)
deriving DecidableEq, Repr, Inhabited

def Offered.admits : Offered → Value → Bool
  | .any, _ => true
  | .listed payloads, v => payloads.contains v

def Offered.payloads : Offered → List Value
  | .any => []
  | .listed payloads => payloads

/--
What each applying offers gives `control`. Only the innermost offering states apply, as in SCXML, where a descendant's
transition wins over an ancestor's.
-/
def offered (st : Service) (s : State) (top : Instance) (control : String) (payload : Value) :
    m (Except Fault (List (Option String × Offered))) := do
  match ← offeringStates fs st s top control payload with
  | .error v => pure (.error v)
  | .ok found =>
  (appliedOffers top control found).foldlM
    (init := (.ok [] : Except Fault (List (Option String × Offered))))
    fun acc (holder, state, o) => do
    match acc with
    | .error v => pure (.error v)
    | .ok done =>
      match o with
      | .any => pure (.ok (done ++ [(state, .any)]))
      | .listed =>
        match ← fs.offers (s.scopeOf holder state) s.records control with
        | .error e =>
          pure (.error (issueViolation st (st.ref top.chart.name) e fun _ =>
            .offersSchema (st.ref top.chart.name) control state))
        | .ok payloads => pure (.ok (done ++ [(state, .listed payloads)]))

/--
The instance that accepts the operation, or the refusal. `payload` is encoded. The operation is accepted if any applying
offers admits the payload, as in SCXML, where an event is handled if any region handles it.
-/
def acceptsOperation (st : Service) (s : State) (resource control : String) (payload : Value) :
    m (Except Fault (Except Refusal Instance)) := do
  match s.accepting resource with
  | .error r => pure (.ok (.error r))
  | .ok top =>
    match ← offered fs st s top control payload with
    | .error v => pure (.error v)
    | .ok applied => pure (.ok (if applied.any (·.2.admits payload) then .ok top else .error .notOffered))

def addValue (acc : List Value) (v : Value) : List Value := if v ∈ acc then acc else acc ++ [v]

/--
The operations that the screen instance `resource` accepts. Offers are evaluated for the payload sent to all copies (without key fields)
and for each copy's key payload, since the key decides which copy receives it. If an applying offers of any of them is
`any`, every payload that matches the schema is accepted (`[{}]` without payload fields); otherwise only offered payloads
that are accepted are listed.
-/
def operationsOf (st : Service) (s : State) (resource : String) :
    m (Except Fault (List Operation)) := do
  match s.accepting resource with
  | .error _ => pure (.ok [])
  | .ok top =>
    let screen := top.chart.name
    let copies := top.copyKeys.flatMap fun (map, cs) =>
      if top.isIn map then cs.filterMap fun k => ((s.machine? (copyName top.resource map k)).bind (·.copyOf)).map (·.key) else []
    top.chart.controls.foldlM (init := (.ok [] : Except Fault (List Operation)))
      fun acc control => do
      match acc with
      | .error v => pure (.error v)
      | .ok done =>
        let applied ← (Value.obj [] :: copies).foldlM
            (init := (.ok [] : Except Fault (List (List (Option String × Offered)))))
            fun acc reach => do
          match acc with
          | .error v => pure (.error v)
          | .ok found =>
            match ← offered fs st s top control.name reach with
            | .error v => pure (.error v)
            | .ok o => pure (.ok (found ++ [o]))
        match applied with
        | .error v => pure (.error v)
        | .ok applied =>
          if applied.any (·.any (·.2 == .any)) then
            pure (.ok (done ++ [{ screen, resource, control := control.name,
                                  payloads := if control.hasPayload then none else some [.obj []] }]))
          else
            let listed := (applied.flatMap fun o => o.flatMap (·.2.payloads)).foldl addValue []
            let kept ← listed.foldlM (init := (.ok [] : Except Fault (List Value)))
              fun acc o => do
              match acc with
              | .error v => pure (.error v)
              | .ok kept =>
                if copies.isEmpty then pure (.ok (kept ++ [o])) else
                match ← acceptsOperation fs st s resource control.name o with
                | .error v => pure (.error v)
                | .ok (.error _) => pure (.ok kept)
                | .ok (.ok _) => pure (.ok (kept ++ [o]))
            match kept with
            | .error v => pure (.error v)
            | .ok [] => pure (.ok done)
            | .ok payloads =>
              pure (.ok (done ++ [{ screen, resource, control := control.name, payloads := some payloads }]))

end Operations

end Tazuna.Service
