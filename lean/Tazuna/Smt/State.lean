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

/-- The key of a slot of the entity `e`: the String variable `x`, or the key fields when they are several. -/
def slotKey (st : Service) (e x : String) : SlotKey :=
  match st.keyFieldsOf e with
  | [_] => .text (strVar x)
  | names => .fields names

/-- The symbolic records of `st` within `creates`, its variables named after `pre`. -/
def SRecords.named (st : Service) (creates : List (String × Nat)) (pre : String) : SRecords :=
  { keyed := (st.entities.filter (!st.singles.contains ·)).map fun e =>
      (e, (List.range ((creates.lookup e).getD 0)).map fun i =>
        let base := s!"{pre}.{e}.{i}"
        { live := boolVar s!"{base}.live", key := slotKey st e s!"{base}.key",
          fields := (fieldsOf st e).map fun f => (f, (fieldVar (entitySchema st e) s!"{base}.{f}" f).1) })
    singles := st.singles.map fun e =>
      (e, (fieldsOf st e).map fun f => (f, (fieldVar (entitySchema st e) s!"{pre}.{e}.{f}" f).1)) }

/-- The variable that tells whether a slot was ever used. -/
def usedVar (pre e : String) (i : Nat) : Term := boolVar s!"{pre}.{e}.{i}.used"

/-- The key field of the keyed entity `e`, none for an entity with several key fields, which slots do not encode. -/
def keyField (st : Service) (e : String) : Option String :=
  match st.structure.body? (st.ref e) with
  | some (.entity { key := some [k], .. }) => some k
  | _ => none

/-- That `a` and `b` hold the same key: equal String keys, or equal values of each key field. -/
def Slot.sameKey (a b : Slot) : Term :=
  match a.key, b.key with
  | .text x, .text y => .eq x y
  | .fields names, _ => conj (names.map fun f => .eq ((a.fields.lookup f).getD undefT) ((b.fields.lookup f).getD undefT))
  | .text _, .fields _ => ff

/-- That the live slots of `slots` have distinct keys. -/
def distinctKeys : List Slot → List Term
  | [] => []
  | s :: ss => ss.map (fun s' => .not (conj [s.live, s'.live, s.sameKey s'])) ++ distinctKeys ss

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
      let keyVar := match s.key with
        | .text _ => [(s!"{pre}.{e}.{i}.key", Ty.str)]
        | .fields _ => []
      facts := facts ++ { vars := [(s!"{pre}.{e}.{i}.live", .bool), (s!"{pre}.{e}.{i}.used", .bool)] ++ keyVar ++ s.fields.flatMap fun (f, _) => (fieldVar (entitySchema st e) s!"{pre}.{e}.{i}.{f}" f).2 }
      let used := usedVar pre e i
      let earlier := if i == 0 then [] else [Term.or (.not used) (usedVar pre e (i - 1))]
      let keyTerm := match keyField st e, s.key with
        | some k, .text t => [Term.eq ((s.fields.lookup k).getD undefT) (.mkStr t)]
        | _, _ => []
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
  { args := (fun | .record => some (.json (SJson.ofTerms fields)) | .now => some (.scalar (.mkInt now)) | _ => none) }

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
  { live := .ite c a.live b.live,
    key := match a.key, b.key with
      | .text x, .text y => .text (.ite c x y)
      | k, _ => k,
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
    { live := .or s.live (chosen i),
      key := match s.key with
        | .text t => .text (.ite (chosen i) key t)
        | k => k,
      fields := s.fields.map fun (f, t) => (f, .ite (chosen i) ((payload.lookup f).getD undefT) t) }
  { records := st.records.mapSlots entity fun _ => slots',
    used := st.used.map fun (e, us) => if e == entity then (e, us.zipIdx.map fun (u, i) => .or u (chosen i)) else (e, us),
    beyond := .or st.beyond ((used.getLast?).getD tt) }

/-- The records after the event `event` with `payload`, as Records.evolve changes them. -/
def Stepped.apply (svc : Service) (st : Stepped) (event : Spec.Ref) (payload : List (String × Term)) : Stepped :=
  let keyOf (fields : List String) : Term := .strOf (match fields with
    | [f] => (payload.lookup f).getD undefT
    | _ => undefT)
  -- A key of several fields is compared field by field (hasPayloadKey), any scalar each.
  let keyGap (fields : List String) : Stepped := match fields with
    | [f] => { st with gap := .or st.gap (.not (.isStr ((payload.lookup f).getD undefT))) }
    | _ => st
  let hasPayloadKey (s : Slot) (key : Term) : Term := match s.key with
    | .text t => .eq t key
    | .fields names => conj (names.map fun f => .eq ((s.fields.lookup f).getD undefT) ((payload.lookup f).getD undefT))
  match svc.changeOf event with
  | some (.create entity keyFields _) => (keyGap keyFields).create entity (keyOf keyFields) payload
  | some (.update entity keyFields _) =>
    let st := keyGap keyFields
    let key := keyOf keyFields
    let slots := (st.records.keyed.lookup entity).getD []
    let hit (s : Slot) := Term.and s.live (hasPayloadKey s key)
    let updated := st.records.mapSlots entity fun ss => ss.map fun s =>
      { s with fields := s.fields.map fun (f, t) => (f, match payload.lookup f with
        | some v => .ite (hit s) v t
        | none => t) }
    let found := disj (slots.map hit)
    Stepped.ite found { st with records := updated } (st.create entity key payload)
  | some (.delete entity keyFields _) =>
    let st := keyGap keyFields
    let key := keyOf keyFields
    { st with records := st.records.mapSlots entity fun ss => ss.map fun s =>
      { s with live := .and s.live (.not (hasPayloadKey s key)) } }
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
      let live ← nameAs s!"{base}.live" .bool s.live
      let key ← match s.key with
        | .text t => do pure (SlotKey.text (← nameAs s!"{base}.key" .str t))
        | k => pure k
      pure ({ live, key,
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

/-- The facts, each holding only where `g` holds. -/
def Facts.under (g : Term) (f : Facts) : Facts := { f with asserts := f.asserts.map (Term.or (.not g)) }

/-- Whether a schema's values may be objects or arrays, which a `V` cannot hold. -/
partial def structured (schema : Value) : Bool :=
  match schema.field? "anyOf" with
  | some (.arr options) => options.any structured
  | _ => schema.field? "type" == some (.str "object") || schema.field? "type" == some (.str "array")

/-- Whether `schema` has no keyword outside `keys` and the descriptive ones, so that the encoding says all it says. -/
def keywordsWithin (schema : Value) (keys : List String) : Bool :=
  match schema with
  | .obj fields => fields.all fun (k, _) => k ∈ keys ++ descriptive
  | _ => false

mutual

/--
A value of `schema` whose variables are named after `x`, each array at most `items` long, and the facts of its schema: a
scalar as propertyVar makes it; an object of its properties; an array of the length `x.len` over `items` items, each
item's facts holding where it is within the length; and a union of objects or arrays by the option `x.option`.
-/
partial def jsonOf (items : Nat) (schema : Value) (x : String) : SJson × Facts :=
  if !structured schema then
    let (t, vars) := propertyVar x ("", schema, true)
    let h := schemaHolds schema t
    (.scalar t, { vars, asserts := [h.term], exact := h.exact, complete := h.complete })
  else match schema.field? "anyOf" with
  | some (.arr options) =>
    let parts := options.zipIdx.map fun (o, i) => (i, jsonOf items o s!"{x}.{i}")
    let option := Term.var s!"{x}.option" .int
    let chosen (i : Nat) := Term.eq option (intLit i)
    let value := match parts.reverse with
      | [] => SJson.scalar undefT
      | (_, last, _) :: rest => rest.foldl (fun acc (i, j, _) => .ite (chosen i) j acc) last
    let facts := parts.foldl (fun acc (i, _, f) => acc ++ f.under (chosen i))
      { vars := [(s!"{x}.option", .int)], asserts := [.le (intLit 0) option, .lt option (intLit options.length)],
        exact := keywordsWithin schema ["anyOf"] }
    (value, facts)
  | _ =>
    if schema.field? "type" == some (.str "object") then
      let (fields, facts) := propertiesOf items schema x
      let own := keywordsWithin schema ["type", "properties", "required", "additionalProperties"]
      (.obj fields, { facts with exact := facts.exact && own })
    else
      let item := (schema.field? "items").getD (.obj [])
      let least := ((schema.field? "minItems").bind intOfValue?).getD 0
      let most : Int := match (schema.field? "maxItems").bind intOfValue? with
        | some m => min m items
        | none => items
      let len := Term.var s!"{x}.len" .int
      let parts := (List.range most.toNat).map fun i => (i, jsonOf items item s!"{x}.{i}")
      -- A set's items are distinct and a sortedBy array's are in key order, which no fact states.
      let exact := keywordsWithin schema ["type", "items", "minItems", "maxItems", "x-tazuna-bag", "x-tazuna-checks"]
      let facts := parts.foldl (fun acc (i, _, f) => acc ++ f.under (.lt (intLit i) len))
        { vars := [(s!"{x}.len", .int)], asserts := [.le (intLit least) len, .le len (intLit most)], exact }
      (.arr len (parts.map (·.2.1)), facts)

/-- The properties of the object schema `schema` as jsonOf makes their values, and their facts. -/
partial def propertiesOf (items : Nat) (schema : Value) (x : String) : List (String × SJson) × Facts :=
  (propertiesWith schema).foldl (init := ([], {})) fun (fields, facts) (n, s, required) =>
    if structured s then
      let (j, f) := jsonOf items s s!"{x}.{n}"
      if required then (fields ++ [(n, j)], facts ++ f)
      else
        let set := boolVar s!"{x}.{n}.set"
        (fields ++ [(n, .ite set j (.scalar undefT))], facts ++ { vars := [(s!"{x}.{n}.set", .bool)] } ++ f.under set)
    else
      let (t, vars) := propertyVar s!"{x}.{n}" (n, s, required)
      let h := fieldHolds t (n, s, required)
      (fields ++ [(n, .scalar t)], facts ++ { vars, asserts := [h.term], exact := h.exact, complete := h.complete })

end

/--
An object of `schema` as JSON holds its fields, each a variable named after `pre`, and that each field fits the schema,
each array within the service's `items` bound.
-/
def objectOf (svc : Service) (schema : Schema) (pre : String) : List (String × SJson) × Facts :=
  propertiesOf (Spec.itemsOf svc.structure.bounds svc.service) ((svc.schemaOf schema).getD (.obj [])) pre

/-- The input of command or query `name` as objectOf makes it. -/
def inputOf (svc : Service) (name : String) (pre : String := "in") : List (String × SJson) × Facts :=
  objectOf svc (.input (svc.ref name)) pre

/--
A caller of a request as JSON holds it, each field a variable named after `pre`: `entity` and `key`, or `service`, the
other fields undefined, as the facts state.
-/
def callerVars (pre : String := "caller") : List (String × Term) × Facts :=
  let fields := ["entity", "key", "service"].map fun f => (f, valVar s!"{pre}.{f}")
  let f (n : String) := (fields.lookup n).getD undefT
  (fields, { vars := fields.map fun (n, _) => (s!"{pre}.{n}", .val),
             asserts := [.or (conj [.isStr (f "entity"), .isStr (f "key"), .isUndef (f "service")])
                           (conj [.isUndef (f "entity"), .isUndef (f "key"), .isStr (f "service")])] })

/-- An entity among `callers` whose key is several fields: its caller key is an object, which callerVars does not hold. -/
def compositeCaller (svc : Service) (callers : List Spec.CallerType) : Option String :=
  callers.findSome? fun
    | .entity e => if (svc.keyFieldsOf e).length > 1 then some e else none
    | .service _ => none

/-- The caller `c` as JSON holds it, a literal. -/
def callerTerms (c : Caller) : List (String × Term) :=
  match c with
  | .entity e (.str k) => [("entity", .mkStr (strLit e)), ("key", .mkStr (strLit k))]
  | .entity e _ => [("entity", .mkStr (strLit e)), ("key", undefT)]
  | .service s => [("service", .mkStr (strLit s))]

/--
That a request to a target that takes `callers` from the caller `caller` passes callerRejection on the records `pre`: the
target lists the caller's kind, and an entity caller's record is live.
-/
def admitted (callers : List Spec.CallerType) (pre : SRecords) (caller : List (String × Term)) : Term :=
  let f (n : String) := (caller.lookup n).getD undefT
  disj (callers.map fun
    | .entity e => conj [.eq (f "entity") (.mkStr (strLit e)), .isStr (f "key"), keyIn (.strOf (f "key")) (pre.slotsOf e)]
    | .service s => .eq (f "service") (.mkStr (strLit s)))

/-- A binding or condition that a request checks in order: its name, the term that holds when its evaluation throws, and its value's term that holds when it passes. -/
structure Check where
  name : String
  throws : Term
  passes : Term

/-- A command's symbolic step from the records `pre`. -/
structure Step where
  facts : Facts
  /-- The input fields, as JSON holds them. -/
  input : List (String × SJson)
  /-- The caller's fields, as JSON holds them. -/
  caller : List (String × Term)
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
  /-- That the command takes the caller (callerRejection), which it checks before the ref fields. -/
  admitted : Term
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
The step of command `name` from `pre` with the input `input` from `caller` at the time `now`, as stepOf builds it; the
variables that name its terms start with `names`, so that two steps can sit in one query.
-/
def stepWith (svc : Service) (p : Program) (pre : SRecords) (used : List (String × List Term)) (name : String)
    (input : List (String × SJson)) (caller : List (String × Term)) (now : Term) (names : String) :
    Except String Step := do
  let some rq := svc.requirements.lookup name | throw s!"no requirements of {name}"
  let facts : Facts := {}
  let args (bound : Option SVal) : Arg → Option SVal
    | .input => some (.json input)
    | .caller => some (.json (SJson.ofTerms caller))
    | .now => some (.scalar (.mkInt now))
    | .bound => bound
    | _ => none
  let env : SEnv := { args := args none, records := pre }
  if let some e := compositeCaller svc rq.callers then throw s!"the caller {e} has a key of several fields"
  let admitted := admitted rq.callers pre caller
  let refs ← rq.refs.filterMapM fun (field, target) => do
    if target.service == svc.service && (pre.keyed.lookup target.name).isSome then
      let v ← match input.lookup field with
        | some (.scalar v) => pure v
        | none => pure undefT
        | some _ => throw s!"the ref field {field}, whose key is several fields"
      pure (some (Term.or (nullishT v) (keyIn (.strOf v) (pre.slotsOf target.name))))
    else pure none
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
  let accepted := conj (admitted :: refs ++ bindTerms.map (held ·.2) ++ requireChecks.map held ++
    [.not decideErr, .not (stepped.records.duplicated svc)])
  pure { facts := facts ++ named, input, caller, now, accepted, post := stepped.records, used := stepped.used,
         beyond := stepped.beyond, gap := .or stepped.gap (stepped.records.outsideSchema svc), bound, admitted,
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
  let (caller, callerFacts) := callerVars
  let now := Term.var "now" .int
  let nowFacts : Facts :=
    { vars := [("now", .int)], asserts := [Term.le (intLit (-maxInstant)) now, .le now (intLit maxInstant), .le clock now] }
  let step ← stepWith svc p pre used name input caller now ""
  pure { step with facts := inputFacts ++ callerFacts ++ nowFacts ++ step.facts }

/-- The term that holds when the ensures `c` of a step's command fails, or throws, after the step. -/
def Step.ensuresFails (step : Step) (c : Condition) : Except String Term := do
  let env : SEnv := { args := (fun | .input => some (.json step.input) | .caller => some (.json (SJson.ofTerms step.caller))
                                    | .bound => some step.bound | _ => none),
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
  input : List (String × SJson)
  /-- The caller's fields, as JSON holds them. -/
  caller : List (String × Term)
  /-- That the query takes the caller (callerRejection), which it checks before its requires. -/
  admitted : Term
  answered : Term
  output : SVal
  /-- The requires, in the order that the query checks them. -/
  requires : List Check

def answerOf (svc : Service) (p : Program) (pre : SRecords) (clock : Term) (name : String) (names : String := "in") :
    Except String Answered := do
  let (input, inputFacts) := inputOf svc name names
  let (caller, callerFacts) := callerVars s!"{names}.caller"
  let callers := ((svc.requirements.lookup name).map (·.callers)).getD []
  let requires := ((p.inputRequirement.find? (·.definition == svc.ref name)).map (·.conditions)).getD []
  let requireChecks ← requires.mapM fun c => do
    let (v, e) ← seval { args := (fun | .input => some (.json input) | _ => none) } [] c.body
    pure ({ name := c.name, throws := e, passes := v.truthy } : Check)
  let some resolve := p.resolve.find? (·.definition == svc.ref name) | throw s!"no resolve of {name}"
  let env : SEnv := { args := (fun | .input => some (.json input) | .caller => some (.json (SJson.ofTerms caller))
                                    | .now => some (.scalar (.mkInt clock)) | _ => none),
                      records := pre }
  let (output, err) ← seval env [] resolve.body
  if let some e := compositeCaller svc callers then throw s!"the caller {e} has a key of several fields"
  let admitted := admitted callers pre caller
  pure { facts := { inputFacts ++ callerFacts with exact := false }, input, caller, admitted,
         answered := conj (admitted :: requireChecks.map (fun c => .and (.not c.throws) c.passes) ++ [.not err]), output,
         requires := requireChecks }

/-- The term that holds when the ensures `c` of a query fails, or throws, on its answer. -/
def Answered.ensuresFails (a : Answered) (pre : SRecords) (c : Condition) : Except String Term := do
  let env : SEnv := { args := (fun | .input => some (.json a.input) | .caller => some (.json (SJson.ofTerms a.caller))
                                    | .output => some a.output | _ => none),
                      records := pre }
  let (v, e) ← seval env [] c.body
  pure (Term.or e (.not v.truthy))

end Tazuna.Smt
