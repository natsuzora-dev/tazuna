import Tazuna.Semantics.Chart.Select

namespace Tazuna.Semantics

open Tazuna.Data

variable {m : Type → Type}

/-- An operation that a screen accepts. `payloads = none` accepts every payload that matches the schema. -/
structure Operation where
  screen : String
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
The instance of `screen` that accepts operations, or the refusal. As with HTML `dialog.showModal()`, a modal blocks the
rest of the page.
-/
def State.accepting (s : State) (screen : String) : Except Refusal Instance :=
  go s.stack.reverse
where
  go : List String → Except Refusal Instance
    | [] => .error .notOpen
    | r :: rest =>
      match s.machine? r with
      | some i =>
        if i.chart.name == screen then .ok i else
        match i.opener with
        | some o => if o.modal then .error (.covered i.chart.name) else go rest
        | none => go rest
      | none => go rest

def offeringStates (st : Service) (s : State) (top : Instance) (control : String) (payload : Value) :
    m (Except Fault (List (Instance × String))) := do
  pure ((← reachedCopies fs st s top payload).map fun reached => top.documentOrder.filterMap fun (h, n) =>
    let holder := if h == top.resource then some top else if h ∈ reached then s.machine? h else none
    holder.bind fun hi => if hi.isIn n && (top.chart.state? n).any (control ∈ ·.offers) then some (hi, n) else none)

def innermostOffers (c : Chart) (found : List (Instance × String)) : List (Instance × String) :=
  let tree := c.tree
  found.filter fun (_, a) => !found.any fun (_, b) => b != a && tree.isDescendant b a

def appliedOffers (top : Instance) (control : String) (found : List (Instance × String)) :
    List (Instance × Option String) :=
  let innermost := innermostOffers top.chart found
  if !innermost.isEmpty || control ∉ top.chart.offers then innermost.map fun (h, n) => (h, some n)
  else [(top, none)]

/--
The payloads that each applying offers lists for `control`. Only the innermost offering states apply, as in SCXML,
where a descendant's transition wins over an ancestor's.
-/
def offered (st : Service) (s : State) (top : Instance) (control : String) (payload : Value) :
    m (Except Fault (List (Option String × List Value))) := do
  match ← offeringStates fs st s top control payload with
  | .error v => pure (.error v)
  | .ok found =>
  (appliedOffers top control found).foldlM
    (init := (.ok [] : Except Fault (List (Option String × List Value))))
    fun acc (holder, state) => do
    match acc with
    | .error v => pure (.error v)
    | .ok done =>
      match ← fs.offers (s.scopeOf holder state) s.records control with
      | .error e =>
        pure (.error (issueViolation st (st.ref top.chart.name) e fun _ =>
          .offersSchema (st.ref top.chart.name) control state))
      | .ok payloads => pure (.ok (done ++ [(state, payloads)]))

/--
The instance that accepts the operation, or the refusal. `payload` is encoded. The operation is accepted if any applying
offers lists the payload, as in SCXML, where an event is handled if any region handles it.
-/
def acceptsOperation (st : Service) (s : State) (screen control : String) (payload : Value) :
    m (Except Fault (Except Refusal Instance)) := do
  match s.accepting screen with
  | .error r => pure (.ok (.error r))
  | .ok top =>
    match ← offered fs st s top control payload with
    | .error v => pure (.error v)
    | .ok [] => pure (.ok (.ok top))
    | .ok applied => pure (.ok (if applied.any (·.2.contains payload) then .ok top else .error .notOffered))

def addValue (acc : List Value) (v : Value) : List Value := if v ∈ acc then acc else acc ++ [v]

/--
The operations that `screen` accepts. Offers are evaluated for the payload sent to all copies (without key fields)
and for each copy's key payload, since the key decides which copy receives it. If any of them has no applicable offers,
every payload that matches the schema is accepted (`[{}]` without payload fields); otherwise only offered payloads that
are accepted are listed.
-/
def operationsOf (st : Service) (s : State) (screen : String) :
    m (Except Fault (List Operation)) := do
  match s.accepting screen with
  | .error _ => pure (.ok [])
  | .ok top =>
    let copies := top.copyKeys.flatMap fun (map, cs) =>
      if top.isIn map then cs.filterMap fun k => ((s.machine? (copyName top.resource map k)).bind (·.copyOf)).map (·.key) else []
    top.chart.controls.foldlM (init := (.ok [] : Except Fault (List Operation)))
      fun acc control => do
      match acc with
      | .error v => pure (.error v)
      | .ok done =>
        let applied ← (Value.obj [] :: copies).foldlM
            (init := (.ok [] : Except Fault (List (List (Option String × List Value)))))
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
          if applied.any (·.isEmpty) then
            pure (.ok (done ++ [{ screen, control := control.name,
                                  payloads := if control.hasPayload then none else some [.obj []] }]))
          else
            let listed := (applied.flatMap fun o => o.flatMap (·.2)).foldl addValue []
            let kept ← listed.foldlM (init := (.ok [] : Except Fault (List Value)))
              fun acc o => do
              match acc with
              | .error v => pure (.error v)
              | .ok kept =>
                if copies.isEmpty then pure (.ok (kept ++ [o])) else
                match ← acceptsOperation fs st s screen control.name o with
                | .error v => pure (.error v)
                | .ok (.error _) => pure (.ok kept)
                | .ok (.ok _) => pure (.ok (kept ++ [o]))
            match kept with
            | .error v => pure (.error v)
            | .ok [] => pure (.ok done)
            | .ok payloads => pure (.ok (done ++ [{ screen, control := control.name, payloads := some payloads }]))

end Operations

end Tazuna.Semantics
