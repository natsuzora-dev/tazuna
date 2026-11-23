import Tazuna.Smt.Encode
import Tazuna.Ir.Functions

/-!
The symbolic records of a service within its bounds, what the semantics guarantees of every state, and a command's step
over them. Each keyed entity has as many slots as its `creates` bound: a slot is used once a record was created in it and
live while the record exists, so keys are never reused. These encodings carry no proof; prove replays each answer that
it reports in the semantics (Prove.replay).
-/

namespace Tazuna.Smt

open Tazuna.Data Tazuna.Ir Tazuna.Service

def boolVar (x : String) : Term := .var x .bool
def strVar (x : String) : Term := .var x .str
def valVar (x : String) : Term := .var x .val

/-- What a symbolic state or step adds: its variables and the terms that must hold. -/
structure Facts where
  vars : List (String × Ty) := []
  asserts : List Term := []
  /-- Whether no term holds of more than the semantics guarantees; otherwise a model may be no state. -/
  exact : Bool := true
  /-- Whether every term holds of every state that the semantics allows; otherwise an unsat answer proves nothing. -/
  complete : Bool := true
deriving Inhabited

instance : Append Facts where
  append a b := { vars := a.vars ++ b.vars, asserts := a.asserts ++ b.asserts, exact := a.exact && b.exact,
                  complete := a.complete && b.complete }

def safeInteger : Int := 9007199254740991

def checksKnown : Value → Bool
  | .arr checks => checks.all fun c => match c.field? "check" with
    | some (Value.str "min_length") | some (Value.str "max_length") => true
    | some (Value.str "number_format") => c.field? "format" == some (Value.str "safeint")
    | some (Value.str "string_format") => c.field? "format" == some (Value.str "date")
    | _ => false
  | _ => false

def descriptive : List String :=
  ["description", "title", "default", "x-tazuna-key", "x-tazuna-nullable", "x-tazuna-checks"]

def intOfValue? : Value → Option Int
  | .num n => if n.exponent == 0 then some n.mantissa else none
  | _ => none

/--
What a term says of the values that a schema accepts. `exact`: it holds of no other value, so a model is a value of the
schema. `complete`: it holds of every value of the schema that a `V` can be; a decimal or an array is none, so a schema
that accepts one is incomplete, and an unsat answer then says nothing of states that hold one.
-/
structure Holds where
  term : Term
  exact : Bool := true
  complete : Bool := true
deriving Inhabited

/--
What holds when the scalar `t` is a value that `schema` accepts. A schema that a scalar cannot fit, such as an object,
holds of no `t`; a keyword outside this subset is left out, so the term holds of more values than the schema accepts.
-/
partial def schemaHolds (schema : Value) (t : Term) : Holds :=
  match schema with
  | .obj fields =>
    let checks := (fields.lookup "x-tazuna-checks").all checksKnown
    let only (keys : List String) := checks && fields.all fun (k, _) => k ∈ keys ++ descriptive
    match fields.lookup "anyOf", fields.lookup "enum", fields.lookup "const", fields.lookup "type" with
    | some (.arr options), _, _, _ =>
      let each := options.map (schemaHolds · t)
      { term := disj (each.map (·.term)), exact := only ["anyOf"] && each.all (·.exact),
        complete := each.all (·.complete) }
    | _, some (.arr values), _, _ =>
      let terms := values.filterMap fun v => (litTerm v).toOption
      { term := disj (terms.map (.eq t ·)), exact := only ["enum", "type"] && terms.length == values.length,
        complete := terms.length == values.length }
    | _, _, some v, _ =>
      match litTerm v with
      | .ok l => { term := .eq t l, exact := only ["const", "type"] }
      | .error _ => { term := tt, exact := false }
    | _, _, _, some types =>
      let names := match types with
        | .str t => [t]
        | .arr ts => ts.filterMap fun | Value.str t => some t | _ => none
        | _ => []
      let bound (key : String) (f : Term → Term) : Term :=
        match (fields.lookup key).bind intOfValue? with
        | some n => f (intLit n)
        | none => tt
      let integer := conj [.isInt t, bound "minimum" (.le · (.intOf t)), bound "maximum" (.le (.intOf t) ·)]
      -- A number is an integer or a decimal; the term holds of the integers, the numbers that a `V` can be.
      -- A date's schema also writes Zod's pattern of its format, which parse checks as parseDate? does.
      let date := fields.lookup "format" == some (.str "date")
      let typed : String → Option (Term × Bool)
        | "string" => some (conj [if date then isDateOf t else .isStr t, bound "minLength" (.le · (.len (.strOf t))),
            bound "maxLength" (.le (.len (.strOf t)) ·)], true)
        | "integer" => some (integer, true)
        | "number" => some (integer, false)
        | "boolean" => some (.isBool t, true)
        | "null" => some (.isNull t, true)
        | _ => none
      let terms := names.filterMap typed
      let complete := terms.length == names.length && terms.all (·.2)
      { term := disj (terms.map (·.1)),
        exact := only (["type", "minLength", "maxLength", "minimum", "maximum"] ++ if date then ["format", "pattern"] else []) &&
          terms.length == names.length &&
          !names.isEmpty,
        complete }
    | _, _, _, none => { term := tt, exact := false }
  | _ => { term := tt, exact := false }

/--
The properties of an object schema, in order, each with whether the object must hold it: a required property, or one with a
default, which parsing fills in.
-/
def propertiesWith (schema : Value) : List (String × Value × Bool) :=
  let required := match schema.field? "required" with
    | some (.arr names) => names.filterMap fun | Value.str n => some n | _ => none
    | _ => []
  match schema.field? "properties" with
  | some (.obj ps) => ps.map fun (n, s) => (n, s, required.contains n || (s.field? "default").isSome)
  | _ => []

/-- That a field holds a value of its schema, or `undefined` when the object may lack it. -/
def fieldHolds (t : Term) : String × Value × Bool → Holds
  | (_, s, required) =>
    let h := schemaHolds s t
    { h with term := if required then h.term else .or (.isUndef t) h.term }

def entitySchema (st : Service) (e : String) : Value := ((st.schemaOf (.record (st.ref e))).getD (.obj []))

def isDateSchema (schema : Value) : Bool :=
  schema.field? "type" == some (.str "string") && schema.field? "format" == some (.str "date")

/--
The term of a variable named `x` that holds a value of the property `p`, and the variables it declares. A date is the
label of an integer day number, so that comparing dates and adding days stay integer arithmetic for the solver; it is
`undefined` instead while its `set` variable is false, when the object may lack it. Any other value is a `V`.
-/
def propertyVar (x : String) (p : String × Value × Bool) : Term × List (String × Ty) :=
  if isDateSchema p.2.1 then
    let label := Term.mkStr (.dateLabel (.var s!"{x}.day" .int))
    if p.2.2 then (label, [(s!"{x}.day", .int)])
    else (.ite (boolVar s!"{x}.set") label undefT, [(s!"{x}.set", .bool), (s!"{x}.day", .int)])
  else (valVar x, [(x, .val)])

/-- The term and variables of the field `f` of an object of schema `schema`, as propertyVar makes them. -/
def fieldVar (schema : Value) (x f : String) : Term × List (String × Ty) :=
  match (propertiesWith schema).find? (·.1 == f) with
  | some p => propertyVar x p
  | none => (valVar x, [(x, .val)])

/-- The symbolic records of `st` within `creates`, its variables named after `pre`. -/
def SRecords.named (st : Service) (creates : List (String × Nat)) (pre : String) : SRecords :=
  { keyed := (st.entities.filter (!st.singles.contains ·)).map fun e =>
      (e, (List.range ((creates.lookup e).getD 0)).map fun i =>
        let base := s!"{pre}.{e}.{i}"
        { live := boolVar s!"{base}.live", key := strVar s!"{base}.key",
          fields := (fieldsOf st e).map fun f => (f, (fieldVar (entitySchema st e) s!"{base}.{f}" f).1) })
    singles := st.singles.map fun e =>
      (e, (fieldsOf st e).map fun f => (f, (fieldVar (entitySchema st e) s!"{pre}.{e}.{f}" f).1)) }

/-- The variable that tells whether a slot was ever used. -/
def usedVar (pre e : String) (i : Nat) : Term := boolVar s!"{pre}.{e}.{i}.used"

def keyField (st : Service) (e : String) : Option String :=
  match st.structure.body? (st.ref e) with
  | some (.entity b) => b.key
  | _ => none

/-- That the live slots of `slots` have distinct keys. -/
def distinctKeys : List Slot → List Term
  | [] => []
  | s :: ss => ss.map (fun s' => .not (conj [s.live, s'.live, .eq s.key s'.key])) ++ distinctKeys ss

/--
That two live slots of `slots` hold the same values of the unique fields `unique`, none of them null. An entity without
unique fields has no clash.
-/
def uniqueClash (unique : List String) : List Slot → List Term
  | [] => []
  | s :: ss =>
    if unique.isEmpty then [] else
    let value (x : Slot) (f : String) := (x.fields.lookup f).getD undefT
    let checked (x : Slot) := conj (unique.map fun f => .not (.isNull (value x f)))
    ss.map (fun s' => conj ([s.live, s'.live, checked s, checked s'] ++ unique.map fun f => .eq (value s f) (value s' f))) ++
      uniqueClash unique ss

/-- The variables of `r` and what the semantics guarantees of every state's records: of every record within its schema. -/
def SRecords.facts (st : Service) (r : SRecords) (pre : String) : Facts := Id.run do
  let mut facts : Facts := {}
  for (e, slots) in r.keyed do
    let props := propertiesWith (entitySchema st e)
    for (s, i) in slots.zipIdx do
      facts := facts ++ { vars := [(s!"{pre}.{e}.{i}.live", .bool), (s!"{pre}.{e}.{i}.used", .bool),
        (s!"{pre}.{e}.{i}.key", .str)] ++ s.fields.flatMap fun (f, _) => (fieldVar (entitySchema st e) s!"{pre}.{e}.{i}.{f}" f).2 }
      let used := usedVar pre e i
      let earlier := if i == 0 then [] else [Term.or (.not used) (usedVar pre e (i - 1))]
      let keyTerm := match keyField st e with
        | some k => [Term.eq ((s.fields.lookup k).getD undefT) (.mkStr s.key)]
        | none => []
      let schemas := props.map fun p => fieldHolds ((s.fields.lookup p.1).getD undefT) p
      let whenLive := (keyTerm ++ schemas.map (·.term)).map (Term.or (.not s.live))
      let asserts := [Term.or (.not s.live) used] ++ earlier ++ whenLive
      facts := facts ++ { asserts, exact := schemas.all (·.exact), complete := schemas.all (·.complete) }
    facts := facts ++ { asserts := distinctKeys slots ++ (uniqueClash (st.uniqueOf e) slots).map .not }
    for (_, field, target) in st.references.filter (·.1 == e) do
      if (r.keyed.lookup target).isSome then
        let targets := r.slotsOf target
        let asserts := slots.map fun s =>
          let v := (s.fields.lookup field).getD undefT
          Term.or (.not (.and s.live (.not (nullishT v)))) (keyIn (.strOf v) targets)
        facts := facts ++ { asserts }
  for (e, fields) in r.singles do
    let props := propertiesWith (entitySchema st e)
    let schemas := props.map fun p => fieldHolds ((fields.lookup p.1).getD undefT) p
    let vars := fields.flatMap fun (f, _) => (fieldVar (entitySchema st e) s!"{pre}.{e}.{f}" f).2
    let asserts := schemas.map (·.term)
    facts := facts ++ { vars, asserts, exact := schemas.all (·.exact), complete := schemas.all (·.complete) }
  return facts

/-- The arguments of an entity invariant: the fields of a record as JSON holds them, and the time, an Int term. -/
def recordEnv (fields : List (String × Term)) (now : Term) : SEnv :=
  { args := (fun | .record => some (.json fields) | .now => some (.scalar (.mkInt now)) | _ => none) }

/-- The arguments of a service invariant: the records and the time, an Int term. -/
def recordsEnv (r : SRecords) (now : Term) : SEnv :=
  { args := (fun | .now => some (.scalar (.mkInt now)) | _ => none), records := r }

/-- The invariants of an entity, by name, that the program holds. -/
def invariantsOf (st : Service) (p : Program) (e : String) : List Condition :=
  ((p.invariant.find? (·.definition == st.ref e)).map (·.conditions)).getD []

def serviceInvariantsOf (st : Service) (p : Program) : List Condition :=
  ((p.serviceInvariant.find? (·.definition == st.ref st.service)).map (·.conditions)).getD []

/-- The slots of `r` with `f` applied to those of `entity`. -/
def SRecords.mapSlots (r : SRecords) (entity : String) (f : List Slot → List Slot) : SRecords :=
  { r with keyed := r.keyed.map fun (e, slots) => if e == entity then (e, f slots) else (e, slots) }

def Slot.ite (c : Term) (a b : Slot) : Slot :=
  { live := .ite c a.live b.live, key := .ite c a.key b.key,
    fields := a.fields.map fun (f, t) => (f, .ite c t ((b.fields.lookup f).getD undefT)) }

def SRecords.ite (c : Term) (a b : SRecords) : SRecords :=
  { keyed := a.keyed.map fun (e, slots) => (e, (slots.zip ((b.keyed.lookup e).getD [])).map fun (x, y) => x.ite c y),
    singles := a.singles.map fun (e, fields) =>
      (e, fields.map fun (f, t) => (f, .ite c t ((((b.singles.lookup e).getD []).lookup f).getD undefT))) }

/--
A step's symbolic state: the records, the slots used so far, the term that holds when the step creates past the bounds,
and the term that holds when it writes what the encoding does not hold, such as a payload field that is no scalar.
-/
structure Stepped where
  records : SRecords
  used : List (String × List Term)
  beyond : Term := ff
  gap : Term := ff

def Stepped.ite (c : Term) (a b : Stepped) : Stepped :=
  { records := .ite c a.records b.records,
    used := a.used.map fun (e, us) => (e, (us.zip ((b.used.lookup e).getD [])).map fun (x, y) => .ite c x y),
    beyond := .ite c a.beyond b.beyond, gap := .ite c a.gap b.gap }

/-- The record that `payload` creates in the first unused slot of `entity`, which leaves the bounds when none is. -/
def Stepped.create (st : Stepped) (entity : String) (key : Term) (payload : List (String × Term)) : Stepped :=
  let slots := (st.records.keyed.lookup entity).getD []
  let used := (st.used.lookup entity).getD []
  let chosen (i : Nat) : Term := conj ([.not ((used[i]?).getD tt)] ++ if i == 0 then [] else [(used[i - 1]?).getD tt])
  let slots' := slots.zipIdx.map fun (s, i) =>
    { live := .or s.live (chosen i), key := .ite (chosen i) key s.key,
      fields := s.fields.map fun (f, t) => (f, .ite (chosen i) ((payload.lookup f).getD undefT) t) }
  { records := st.records.mapSlots entity fun _ => slots',
    used := st.used.map fun (e, us) => if e == entity then (e, us.zipIdx.map fun (u, i) => .or u (chosen i)) else (e, us),
    beyond := .or st.beyond ((used.getLast?).getD tt) }

/-- The records after the event `event` with `payload`, as Records.evolve changes them. -/
def Stepped.apply (svc : Service) (st : Stepped) (event : Spec.Ref) (payload : List (String × Term)) : Stepped :=
  let keyOf (field : String) : Term := .strOf ((payload.lookup field).getD undefT)
  let keyGap (field : String) : Stepped := { st with gap := .or st.gap (.not (.isStr ((payload.lookup field).getD undefT))) }
  match svc.changeOf event with
  | some (.create entity keyField _) => (keyGap keyField).create entity (keyOf keyField) payload
  | some (.update entity keyField _) =>
    let st := keyGap keyField
    let key := keyOf keyField
    let slots := (st.records.keyed.lookup entity).getD []
    let hit (s : Slot) := Term.and s.live (.eq s.key key)
    let updated := st.records.mapSlots entity fun ss => ss.map fun s =>
      { s with fields := s.fields.map fun (f, t) => (f, match payload.lookup f with
        | some v => .ite (hit s) v t
        | none => t) }
    let found := disj (slots.map hit)
    Stepped.ite found { st with records := updated } (st.create entity key payload)
  | some (.delete entity keyField _) =>
    let st := keyGap keyField
    let key := keyOf keyField
    { st with records := st.records.mapSlots entity fun ss => ss.map fun s =>
      { s with live := .and s.live (.not (.eq s.key key)) } }
  | some (.set entity _) =>
    { st with records := { st.records with singles := st.records.singles.map fun (e, fields) =>
      if e == entity then (e, fields.map fun (f, t) => (f, (payload.lookup f).getD t)) else (e, fields) } }
  | _ => st

/-- Terms that named variables stand for, which keep the terms of later events small: each name and what it equals. -/
abbrev Named := StateM (List (String × Ty × Term))

/-- `t` as the variable `x` that equals it, or `t` itself when it is a variable or a literal already. -/
def nameAs (x : String) (ty : Ty) (t : Term) : Named Term :=
  match t with
  | .var .. | .lit _ => pure t
  | _ => do modify (· ++ [(x, ty, t)]); pure (.var x ty)

/--
A value term that is a date or `undefined` in each branch, with at least one date (propertyVar's shape after steps): the
term that holds when it is a date, and its day number.
-/
def dayView? : Term → Option (Term × Term × Bool)
  | .mkStr (.dateLabel z) => some (tt, z, true)
  | .lit (.val .undef) => some (ff, intLit 0, false)
  | .ite c a b => do
    let (sa, za, la) ← dayView? a
    let (sb, zb, lb) ← dayView? b
    pure (.ite c sa sb, .ite c za zb, la || lb)
  | _ => none

/-- The value term `t` as named variables: a date (dayView?) by its day number and whether it is set, as propertyVar. -/
def nameValue (x : String) (t : Term) : Named Term :=
  match dayView? t with
  | some (set, z, true) => do
    let label := Term.mkStr (.dateLabel (← nameAs s!"{x}.day" .int z))
    match set with
    | .lit (.bool true) => pure label
    | _ => pure (.ite (← nameAs s!"{x}.set" .bool set) label undefT)
  | _ => nameAs x .val t

/-- The state with each of its terms named after `p`. -/
def Stepped.named (st : Stepped) (p : String) : Named Stepped := do
  let keyed ← st.records.keyed.mapM fun (e, slots) => do
    let slots ← slots.zipIdx.mapM fun (s, i) => do
      let base := s!"{p}.{e}.{i}"
      pure ({ live := ← nameAs s!"{base}.live" .bool s.live, key := ← nameAs s!"{base}.key" .str s.key,
              fields := ← s.fields.mapM fun (f, t) => do pure (f, ← nameValue s!"{base}.{f}" t) } : Slot)
    pure (e, slots)
  let singles ← st.records.singles.mapM fun (e, fields) => do
    pure (e, ← fields.mapM fun (f, t) => do pure (f, ← nameValue s!"{p}.{e}.{f}" t))
  let used ← st.used.mapM fun (e, us) => do
    pure (e, ← us.zipIdx.mapM fun (u, i) => nameAs s!"{p}.{e}.{i}.used" .bool u)
  pure { records := { keyed, singles }, used, beyond := ← nameAs s!"{p}.beyond" .bool st.beyond,
         gap := ← nameAs s!"{p}.gap" .bool st.gap }

/-- The payload of an emit as scalar fields, and the term that holds when one is no scalar. -/
def payloadOf : SVal → Except String (List (String × Term) × Term)
  | .obj fields => pure (fields.map (fun (f, v) => (f, v.scalarOf.1)), disj (fields.map (·.2.scalarOf.2)))
  | _ => throw "an emit whose payload is no object literal"

/-- The records after the emits of `item`, which is an emit or a choice between emits; `p` names its payloads. -/
def Stepped.emitAll (svc : Service) (p : String) : Stepped → SVal → ExceptT String Named Stepped
  | st, .emit event payload => do
    let (fields, notScalar) ← payloadOf payload
    let fields ← fields.mapM fun (f, t) => do pure (f, ← (nameValue s!"{p}.{event.name}.{f}" t : Named Term))
    let st' := st.apply svc event fields
    pure { st' with gap := .or st'.gap notScalar }
  | st, .ite c a b => do pure (.ite c (← st.emitAll svc s!"{p}.y" a) (← st.emitAll svc s!"{p}.n" b))
  | _, _ => throw "a decide item that is no emit"

/-- That two live records of an entity of `r` clash on their key or unique fields (Integrity.duplicated). -/
def SRecords.duplicated (svc : Service) (r : SRecords) : Term :=
  disj (r.keyed.flatMap fun (e, slots) =>
    ((distinctKeys slots).map .not) ++ uniqueClash (svc.uniqueOf e) slots)

/-- That some live record of `r` holds a field outside its entity's schema. -/
def SRecords.outsideSchema (svc : Service) (r : SRecords) : Term :=
  disj (r.keyed.flatMap fun (e, slots) =>
      let props := propertiesWith (entitySchema svc e)
      slots.flatMap fun s => props.map fun p => conj [s.live, .not (fieldHolds ((s.fields.lookup p.1).getD undefT) p).term]) |>.or
    (disj (r.singles.flatMap fun (e, fields) =>
      (propertiesWith (entitySchema svc e)).map fun p => .not (fieldHolds ((fields.lookup p.1).getD undefT) p).term))

/--
An object of `schema` as JSON holds its fields, each a variable named after `pre`, and that each field fits the schema.
-/
def objectOf (svc : Service) (schema : Schema) (pre : String) : List (String × Term) × Facts :=
  let props := propertiesWith ((svc.schemaOf schema).getD (.obj []))
  let terms := props.map fun pr => (pr.1, propertyVar s!"{pre}.{pr.1}" pr)
  let input := terms.map fun (f, t, _) => (f, t)
  let fieldFacts := props.map fun pr => fieldHolds ((input.lookup pr.1).getD undefT) pr
  (input, { vars := terms.flatMap (·.2.2), asserts := fieldFacts.map (·.term),
            exact := fieldFacts.all (·.exact), complete := fieldFacts.all (·.complete) })

/-- The input of command or query `name` as objectOf makes it. -/
def inputOf (svc : Service) (name : String) (pre : String := "in") : List (String × Term) × Facts :=
  objectOf svc (.input (svc.ref name)) pre

/-- A binding or condition that a request checks in order: its name, the term that holds when its evaluation throws, and its value's term that holds when it passes. -/
structure Check where
  name : String
  throws : Term
  passes : Term

/-- A command's symbolic step from the records `pre`. -/
structure Step where
  facts : Facts
  /-- The input fields, as JSON holds them. -/
  input : List (String × Term)
  now : Term
  /-- That the command accepts: no rejection and no throw before the integrity check. -/
  accepted : Term
  post : SRecords
  /-- The slots of each entity used after the step. -/
  used : List (String × List Term)
  /-- That the step creates past the bounds. -/
  beyond : Term
  /-- That the step writes what the encoding does not hold, or a record outside its schema. -/
  gap : Term
  /-- The binds values, from the records before the step, as the command's ensures reads them. -/
  bound : SVal
  /-- That every ref field of the input names a record, which the command checks before its binds. -/
  refs : Term
  /-- The binds, a value that is not null passing, then the requires, each in the order that the command checks them. -/
  binds : List Check
  requires : List Check
  /-- For each path through the decide's choices between emits, the term that holds when the step takes it. -/
  paths : List Term

/-- The paths through a decide item's choices between emits, each as the term that holds when it is taken. -/
def emitPaths : SVal → List Term
  | .ite c a b => (emitPaths a).map (.and c) ++ (emitPaths b).map (.and (.not c))
  | _ => [tt]

/--
The step of command `name` from `pre` with the input `input` at the time `now`, as stepOf builds it; the variables that
name its terms start with `names`, so that two steps can sit in one query.
-/
def stepWith (svc : Service) (p : Program) (pre : SRecords) (used : List (String × List Term)) (name : String)
    (input : List (String × Term)) (now : Term) (names : String) : Except String Step := do
  let some rq := svc.requirements.lookup name | throw s!"no requirements of {name}"
  let facts : Facts := {}
  let args (bound : Option SVal) : Arg → Option SVal
    | .input => some (.json input)
    | .now => some (.scalar (.mkInt now))
    | .bound => bound
    | _ => none
  let env : SEnv := { args := args none, records := pre }
  let refs := rq.refs.filterMap fun (field, target) =>
    if target.service == svc.service && (pre.keyed.lookup target.name).isSome then
      let v := (input.lookup field).getD undefT
      some (Term.or (nullishT v) (keyIn (.strOf v) (pre.slotsOf target.name)))
    else none
  let binds := ((p.binding.find? (·.definition == svc.ref name)).map (·.conditions)).getD []
  let bindTerms ← binds.mapM fun b => do
    let (v, e) ← seval env [] b.body
    pure (v, ({ name := b.name, throws := e, passes := .not v.nullish } : Check))
  let bound : SVal := .obj (bindTerms.map fun (v, c) => (c.name, v))
  let env := { env with args := args (some bound) }
  let requires := ((p.requirement.find? (·.definition == svc.ref name)).map (·.conditions)).getD []
  let requireChecks ← requires.mapM fun c => do
    let (v, e) ← seval env [] c.body
    pure ({ name := c.name, throws := e, passes := v.truthy } : Check)
  let held (c : Check) := Term.and (.not c.throws) c.passes
  let some decide := p.decide.find? (·.definition == svc.ref name) | throw s!"no decide of {name}"
  let (decided, decideErr) ← seval env [] decide.body
  let items ← match decided with
    | .list items => pure items
    | _ => throw "a decide that returns no array literal"
  let start : Stepped := { records := pre, used }
  let applied : ExceptT String Named Stepped := items.zipIdx.foldlM (init := start) fun st (item, k) => do
    let st ← st.emitAll svc s!"{names}emit{k}" item
    (st.named s!"{names}post{k}" : Named Stepped)
  let (stepped, defs) := applied.run.run []
  let stepped ← stepped
  let named : Facts := { vars := defs.map fun (x, ty, _) => (x, ty), asserts := defs.map fun (x, ty, t) => .eq (.var x ty) t }
  let accepted := conj (refs ++ bindTerms.map (held ·.2) ++ requireChecks.map held ++
    [.not decideErr, .not (stepped.records.duplicated svc)])
  pure { facts := facts ++ named, input, now, accepted, post := stepped.records, used := stepped.used,
         beyond := stepped.beyond, gap := .or stepped.gap (stepped.records.outsideSchema svc), bound,
         refs := conj refs, binds := bindTerms.map (·.2), requires := requireChecks,
         paths := items.foldl (fun acc item => acc.flatMap fun p => (emitPaths item).map (.and p)) [tt] }

/--
The step of command `name` of `svc` from `pre` at the time `clock`, whose slots of each entity are used as `used` says.
The step's time is no earlier than `clock`: the semantics never moves time back (Sim's clock line reports `notLater`,
and verify's replay keeps the later time), which no theorem states yet.
-/
def stepOf (svc : Service) (p : Program) (pre : SRecords) (clock : Term) (used : List (String × List Term))
    (name : String) : Except String Step := do
  let (input, inputFacts) := inputOf svc name
  let now := Term.var "now" .int
  let nowFacts : Facts :=
    { vars := [("now", .int)], asserts := [Term.le (intLit (-safeInteger)) now, .le now (intLit safeInteger), .le clock now] }
  let step ← stepWith svc p pre used name input now ""
  pure { step with facts := inputFacts ++ nowFacts ++ step.facts }

/-- The term that holds when the ensures `c` of a step's command fails, or throws, after the step. -/
def Step.ensuresFails (step : Step) (c : Condition) : Except String Term := do
  let env : SEnv := { args := (fun | .input => some (.json step.input) | .bound => some step.bound | _ => none),
                      records := step.post }
  let (v, e) ← seval env [] c.body
  pure (Term.or e (.not v.truthy))

/-- The term that holds when a live record of `entity` in `r` holds in `field` a key that no live record of `target` has. -/
def SRecords.dangling (r : SRecords) (entity field target : String) : Term :=
  let danglingAt (live : Term) (fields : List (String × Term)) : Term :=
    let v := (fields.lookup field).getD undefT
    conj [live, .not (nullishT v), .or (.not (.isStr v)) (.not (keyIn (.strOf v) (r.slotsOf target)))]
  disj ((r.slotsOf entity).map (fun s => danglingAt s.live s.fields) ++ ((r.singles.lookup entity).map (danglingAt tt)).toList)

/--
A query's symbolic answer on the records `pre` at the time `clock`: its input, the term that holds when the input passes
the query's requires and resolve does not throw, and the output. The facts are inexact: nothing states that the output
fits its schema, which the semantics checks before the ensures read it.
-/
structure Answered where
  facts : Facts
  input : List (String × Term)
  answered : Term
  output : SVal
  /-- The requires, in the order that the query checks them. -/
  requires : List Check

def answerOf (svc : Service) (p : Program) (pre : SRecords) (clock : Term) (name : String) (names : String := "in") :
    Except String Answered := do
  let (input, inputFacts) := inputOf svc name names
  let requires := ((p.inputRequirement.find? (·.definition == svc.ref name)).map (·.conditions)).getD []
  let requireChecks ← requires.mapM fun c => do
    let (v, e) ← seval { args := (fun | .input => some (.json input) | _ => none) } [] c.body
    pure ({ name := c.name, throws := e, passes := v.truthy } : Check)
  let some resolve := p.resolve.find? (·.definition == svc.ref name) | throw s!"no resolve of {name}"
  let env : SEnv := { args := (fun | .input => some (.json input) | .now => some (.scalar (.mkInt clock)) | _ => none),
                      records := pre }
  let (output, err) ← seval env [] resolve.body
  pure { facts := { inputFacts with exact := false }, input,
         answered := conj (requireChecks.map (fun c => .and (.not c.throws) c.passes) ++ [.not err]), output,
         requires := requireChecks }

/-- The term that holds when the ensures `c` of a query fails, or throws, on its answer. -/
def Answered.ensuresFails (a : Answered) (pre : SRecords) (c : Condition) : Except String Term := do
  let env : SEnv := { args := (fun | .input => some (.json a.input) | .output => some a.output | _ => none),
                      records := pre }
  let (v, e) ← seval env [] c.body
  pure (Term.or e (.not v.truthy))

end Tazuna.Smt
