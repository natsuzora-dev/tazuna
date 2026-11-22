import Tazuna.Data.Binary64
import Tazuna.Data.Time
import Tazuna.Data.UnionOptions

/-!
Parsing a value by its JSON Schema as Zod's safeParse does, for the schemas whose JSON Schema says all that Zod checks
(`supported`): the value that the parse gives, encoded again as JSON, or the issues that Zod reports, field for field
and in Zod's order. TS writes what JSON Schema leaves out as `x-tazuna-*` keywords: the checks in Zod's order, a
nullable, a discriminator, and `x-tazuna-opaque` where only Zod knows what happens.
-/

namespace Tazuna.Data

/--
An issue as Zod reports it: its fields in Zod's order, where `path` and `message` sit only when Zod made the issue
with them, then its path and its message. `continues` is the issue's `continue`, which tells whether later checks run.
`own` tells whether the schema being parsed made it, not a schema inside it, so the schema's message applies, and
`authored` whether a check gave it its own message, which the schema's does not replace.
-/
structure ZodIssue where
  fields : List (String × Value)
  path : List Value := []
  message : String
  continues : Option Bool := none
  own : Bool := true
  authored : Bool := false
deriving Inhabited

def ZodIssue.under (key : Value) (i : ZodIssue) : ZodIssue := { i with path := key :: i.path, own := false }

/-- The issue as Zod's finalizeIssue writes it: a path and a message that the issue lacks come last. -/
def ZodIssue.render (i : ZodIssue) : Value :=
  let filled := i.fields.map fun (k, v) =>
    if k == "path" then (k, .arr i.path) else if k == "message" then (k, .str i.message) else (k, v)
  let path := if i.fields.any (·.1 == "path") then [] else [("path", .arr i.path)]
  let message := if i.fields.any (·.1 == "message") then [] else [("message", .str i.message)]
  .obj (filled ++ path ++ message)

/-- What parsing gives: the value, none for undefined, and the issues. -/
structure Parsed where
  value : Option Value
  issues : List ZodIssue := []
deriving Inhabited

/-- The parse of a schema inside the one being parsed, whose issues that schema made. -/
def Parsed.passed (p : Parsed) : Parsed := { p with issues := p.issues.map ({ · with own := false }) }

/-- Whether a check without a `when` is skipped, as Zod's util.aborted: an issue that does not say it continues. -/
def aborted (issues : List ZodIssue) : Bool := issues.any (·.continues != some true)

/-- Whether even a check with a `when` is skipped, as Zod's util.explicitlyAborted: an issue that says it stops. -/
def explicitlyAborted (issues : List ZodIssue) : Bool := issues.any (·.continues == some false)

/-- An author's code or a codec's transform threw, as a refinement can. -/
abbrev ParseM := Except Unit

/-- The type that Zod's util.parsedType names for a value, `undefined` for none. -/
def parsedType : Option Value → String
  | none => "undefined"
  | some .null => "null"
  | some (.bool _) => "boolean"
  | some (.num _) => "number"
  | some (.str _) => "string"
  | some (.arr _) => "array"
  | some (.obj _) => "object"

/-- A value as Zod's util.stringifyPrimitive writes it in a message. -/
def primitiveText : Value → String
  | .str s => "\"" ++ s ++ "\""
  | .num n => jsNumber n
  | .bool b => toString b
  | .null => "null"
  | v => v.canonical

def scalarText : Value → String
  | .str s => s
  | v => primitiveText v

def invalidType (expected : String) (v : Option Value) : ZodIssue :=
  { fields := [("expected", .str expected), ("code", .str "invalid_type")]
    message := s!"Invalid input: expected {expected}, received {parsedType v}" }

/-- The issue of a required field that is absent and whose schema takes undefined. -/
def nonoptional (key : String) : ZodIssue :=
  { fields := [("code", .str "invalid_type"), ("expected", .str "nonoptional"), ("path", .null)]
    path := [.str key]
    message := "Invalid input: expected nonoptional, received undefined" }

/-- Numbers equal as JS numbers, other values as JSON. -/
def sameValue : Value → Value → Bool
  | .num a, .num b => a.mantissa * 10 ^ b.exponent == b.mantissa * 10 ^ a.exponent
  | a, b => a == b

def numLt (a b : Lean.JsonNumber) : Bool := a.mantissa * 10 ^ b.exponent < b.mantissa * 10 ^ a.exponent

/-- A number as JS writes it back to JSON. -/
def jsonNumber (n : Lean.JsonNumber) : Lean.JsonNumber := (decimalOf? n.toFloat).getD n

def isInteger (n : Lean.JsonNumber) : Bool := n.mantissa % 10 ^ n.exponent == 0

def safeLimit : Int := 2 ^ 53 - 1

/-- Zod's util.floatSafeRemainder of two doubles is zero. -/
def multipleOf (value step : Float) : Bool :=
  let ratio := value / step
  let floor := ratio.floor
  let rounded := if ratio - floor >= 0.5 then floor + 1 else floor
  let magnitude := if ratio.abs > 1 then ratio.abs else 1
  (ratio - rounded).abs < 4 * 2.220446049250313e-16 * magnitude

/-- Zod's pattern of z.iso.date(), as an issue writes it. -/
def datePattern : String :=
  "(?:(?:\\d\\d[2468][048]|\\d\\d[13579][26]|\\d\\d0[48]|[02468][048]00|[13579][26]00)-02-29|\\d{4}-(?:(?:0[13578]|1[02])-(?:0[1-9]|[12]\\d|3[01])|(?:0[469]|11)-(?:0[1-9]|[12]\\d|30)|(?:02)-(?:0[1-9]|1\\d|2[0-8])))"


def fieldStr (schema : Value) (key : String) : Option String :=
  match schema.field? key with
  | some (.str s) => some s
  | _ => none

def checksOf (schema : Value) : List Value :=
  match schema.field? "x-tazuna-checks" with
  | some (.arr checks) => checks
  | _ => []

/-- Whether Lean runs `check` as Zod does. -/
def supportedCheck (c : Value) : Bool :=
  match fieldStr c "check" with
  | some "min_length" | some "max_length" | some "length_equals" | some "greater_than" | some "less_than"
  | some "multiple_of" | some "set" => true
  | some "number_format" => fieldStr c "format" == some "safeint"
  | some "string_format" =>
    match fieldStr c "format" with
    | some "starts_with" | some "ends_with" => true
    | some "includes" => c.field? "position" == none
    | some "date" => true
    | _ => false
  | _ => false

/-- The keywords that parse reads or that change nothing that Zod checks. -/
def knownKeywords : List String :=
  ["$schema", "type", "properties", "required", "additionalProperties", "items", "minItems", "maxItems", "minLength",
   "maxLength", "minimum", "maximum", "exclusiveMinimum", "exclusiveMaximum", "multipleOf", "format", "pattern",
   "enum", "const", "anyOf", "oneOf", "default", "uniqueItems", "description", "title", "examples",
   "x-tazuna-checks", "x-tazuna-nullable", "x-tazuna-discriminator", "x-tazuna-message", "x-tazuna-bag",
   "x-tazuna-set", "x-tazuna-sorted-by"]

/-- Whether an `allOf` holds only the patterns that JSON Schema writes for several string checks, as the checks say. -/
def patternsOnly : Value → Bool
  | .arr parts => parts.all fun
    | .obj [("pattern", _)] => true
    | _ => false
  | _ => false

/-- The options of a union: its anyOf or oneOf, or one option per name of a `type` list. -/
def optionsOf (schema : Value) : Option (List Value) :=
  match unionOptions schema, schema.field? "type" with
  | some options, _ => some options
  | none, some (.arr types) => some (types.map fun t => .obj [("type", t)])
  | none, _ => none

/-- What a nullable wraps: the option of its union that is not null. -/
def nullableInner (schema : Value) : Value :=
  let notNull (o : Value) := o.field? "type" != some (.str "null")
  match optionsOf schema with
  | some options => ((options.filter notNull).head?).getD (.obj [])
  | none => schema

/-- Whether `schema` says all that Zod checks, at every depth, so that Lean parses as Zod does. -/
partial def supported (schema : Value) : Bool :=
  match schema with
  | .obj fields =>
    fields.all (fun (k, v) => knownKeywords.contains k || (k == "allOf" && patternsOnly v)) &&
    (checksOf schema).all supportedCheck &&
    (match schema.field? "additionalProperties" with
      | none | some (.bool false) => true
      | _ => false) &&
    (if schema.field? "x-tazuna-nullable" == some (.bool true) then supported (nullableInner schema) else
      (match optionsOf schema with
        | some options =>
          options.all supported &&
          (schema.field? "oneOf" == none || (fieldStr schema "x-tazuna-discriminator").isSome)
        | none => true) &&
      (match schema.field? "properties" with
        | some (.obj ps) => ps.all fun (_, p) => supported p
        | some _ => false
        | none => true) &&
      (match schema.field? "items" with
        | some item => supported item
        | none => true))
  | _ => false

/-- An issue of a check, which continues to later checks, as Zod's checks write `continue: !def.abort`. -/
def checkIssue (fields : List (String × Value)) (message : String) : ZodIssue :=
  { fields, message, continues := some true }

def sizing (origin : String) : Option String :=
  match origin with
  | "string" => some "characters"
  | "array" => some "items"
  | _ => none

def boundMessage (big : Bool) (origin : String) (adjective : String) (bound : Value) : String :=
  let size := match bound with | .num n => jsNumber n | v => scalarText v
  let head := if big then "Too big" else "Too small"
  match sizing origin with
  | some unit => s!"{head}: expected {origin} to have {adjective}{size} {unit}"
  | none => s!"{head}: expected {origin} to be {adjective}{size}"

def lengthOf : Value → Option Nat
  | .str s => some s.length
  | .arr vs => some vs.length
  | _ => none

def originOf : Value → String
  | .arr _ => "array"
  | .str _ => "string"
  | _ => "unknown"

/-- The issues of one check on `v`, which the type took. -/
def checkIssues (c : Value) (v : Value) : List ZodIssue :=
  let num (k : String) : Lean.JsonNumber := match c.field? k with | some (.num n) => n | _ => 0
  let nat (k : String) : Nat := (num k).mantissa.toNat
  let inclusive := c.field? "inclusive" != some (.bool false)
  let adjective (big : Bool) := if inclusive then (if big then "<=" else ">=") else (if big then "<" else ">")
  match fieldStr c "check", v with
  | some "min_length", _ =>
    match lengthOf v with
    | some n => if n ≥ nat "minimum" then [] else
      [checkIssue [("origin", .str (originOf v)), ("code", .str "too_small"), ("minimum", .num (num "minimum")),
        ("inclusive", .bool true)] (boundMessage false (originOf v) ">=" (.num (num "minimum")))]
    | none => []
  | some "max_length", _ =>
    match lengthOf v with
    | some n => if n ≤ nat "maximum" then [] else
      [checkIssue [("origin", .str (originOf v)), ("code", .str "too_big"), ("maximum", .num (num "maximum")),
        ("inclusive", .bool true)] (boundMessage true (originOf v) "<=" (.num (num "maximum")))]
    | none => []
  | some "length_equals", _ =>
    match lengthOf v with
    | some n =>
      let length := nat "length"
      if n == length then [] else
      let big := n > length
      [checkIssue ([("origin", .str (originOf v))] ++
          (if big then [("code", .str "too_big"), ("maximum", .num length)]
           else [("code", .str "too_small"), ("minimum", .num length)]) ++
          [("inclusive", .bool true), ("exact", .bool true)])
        (boundMessage big (originOf v) "exactly " (.num length))]
    | none => []
  | some "greater_than", .num n =>
    let bound := num "value"
    if (if inclusive then !numLt n bound else numLt bound n) then [] else
    [checkIssue [("origin", .str "number"), ("code", .str "too_small"), ("minimum", .num bound),
      ("inclusive", .bool inclusive)] (boundMessage false "number" (adjective false) (.num bound))]
  | some "less_than", .num n =>
    let bound := num "value"
    if (if inclusive then !numLt bound n else numLt n bound) then [] else
    [checkIssue [("origin", .str "number"), ("code", .str "too_big"), ("maximum", .num bound),
      ("inclusive", .bool inclusive)] (boundMessage true "number" (adjective true) (.num bound))]
  | some "multiple_of", .num n =>
    if multipleOf n.toFloat (num "value").toFloat then [] else
    [checkIssue [("origin", .str "number"), ("code", .str "not_multiple_of"), ("divisor", .num (num "value"))]
      s!"Invalid number: must be a multiple of {jsNumber (num "value")}"]
  | some "number_format", .num n =>
    let abort := c.field? "abort" == some (.bool true)
    if !isInteger n then
      [{ fields := [("expected", .str "int"), ("format", .str "safeint"), ("code", .str "invalid_type")]
         message := "Invalid input: expected int, received number", continues := some false }]
    else
      let i := n.mantissa / 10 ^ n.exponent
      let note : Value := .str "Integers must be within the safe integer range."
      if i > safeLimit then
        [{ fields := [("code", .str "too_big"), ("maximum", .num safeLimit), ("note", note), ("origin", .str "int"),
            ("inclusive", .bool true)]
           message := s!"Too big: expected int to be <={safeLimit}", continues := some !abort }]
      else if i < -safeLimit then
        [{ fields := [("code", .str "too_small"), ("minimum", .num (-safeLimit)), ("note", note),
            ("origin", .str "int"), ("inclusive", .bool true)]
           message := s!"Too small: expected int to be >={-safeLimit}", continues := some !abort }]
      else []
  | some "string_format", .str s =>
    let format := (fieldStr c "format").getD ""
    let failed (key : String) (expected : String) (verb : String) : List ZodIssue :=
      [checkIssue [("origin", .str "string"), ("code", .str "invalid_format"), ("format", .str format),
        (key, .str expected)] s!"Invalid string: must {verb} \"{expected}\""]
    match format with
    | "starts_with" =>
      let p := (fieldStr c "prefix").getD ""
      if p.toList.isPrefixOf s.toList then [] else failed "prefix" p "start with"
    | "ends_with" =>
      let p := (fieldStr c "suffix").getD ""
      if p.toList.reverse.isPrefixOf s.toList.reverse then [] else failed "suffix" p "end with"
    | "includes" =>
      let p := (fieldStr c "includes").getD ""
      if (List.range (s.length + 1)).any (fun i => p.toList.isPrefixOf (s.toList.drop i)) then []
      else failed "includes" p "include"
    | _ =>
      if (parseDate? s).isSome then [] else
      [checkIssue [("origin", .str "string"), ("code", .str "invalid_format"), ("format", .str format),
        ("pattern", .str ("/^" ++ datePattern ++ "$/"))] "Invalid ISO date"]
  | some "set", .arr vs =>
    let (_, issues) := vs.zipIdx.foldl (fun ((seen : List String), (issues : List ZodIssue)) (x, i) =>
      let text := x.canonical
      (seen ++ [text], if seen.contains text then
        issues ++ [{ fields := [("code", .str "custom"), ("message", .str ""), ("path", .null)], path := [.num i]
                     message := s!"duplicate element {text}" }]
       else issues)) ([], [])
    issues
  | _, _ => []

/-- The issues of the check `c` on `v`, with the check's own message and abort, as Zod's check parameters give them. -/
def runCheck (c : Value) (v : Value) : List ZodIssue :=
  (checkIssues c v).map fun i =>
    let i := if c.field? "abort" == some (.bool true) then { i with continues := some false } else i
    match fieldStr c "message" with
    | some m => { i with message := m, authored := true }
    | none => i

/-- Whether a check runs only on a value with a length, after any issue that does not say it stops (Zod's `when`). -/
def hasWhen (c : Value) : Bool :=
  match fieldStr c "check" with
  | some "min_length" | some "max_length" | some "length_equals" => true
  | _ => false

/-- The issues after Zod's runChecks of `checks` on `p`. -/
def runChecks (checks : List Value) (p : Parsed) : Parsed :=
  match p.value with
  | none => p
  | some v =>
    let (_, issues) := checks.foldl (fun ((stopped : Bool), (issues : List ZodIssue)) c =>
      if hasWhen c then
        if explicitlyAborted issues || (lengthOf v).isNone then (stopped, issues)
        else
          let found := runCheck c v
          (stopped || aborted found, issues ++ found)
      else if stopped then (stopped, issues)
      else
        let found := runCheck c v
        (aborted found, issues ++ found)) (aborted p.issues, p.issues)
    { p with issues }

/--
The upper bounds of the leading length checks, each with its check: an array longer than one of them fails that check
alone, as Zod's capSize stops before it parses the elements.
-/
def sizeCaps (checks : List Value) : List (Value × Nat) :=
  (checks.takeWhile hasWhen).filterMap fun c =>
    match fieldStr c "check", c.field? "maximum", c.field? "length" with
    | some "max_length", some (.num n), _ | some "length_equals", _, some (.num n) => some (c, n.mantissa.toNat)
    | _, _, _ => none

/-- The discriminator values of an option: its field's `const` or `enum`. -/
def discriminatorValues (key : String) (option : Value) : List Value :=
  match propertyOf option key with
  | some p => (allowed p).getD []
  | none => []

mutual

/-- `v` parsed by `schema` as Zod's safeParse does, with the schema's own message on the issues that it makes. -/
partial def parseValue (schema : Value) (v : Option Value) : ParseM Parsed := do
  let p ← parseNode schema v
  match fieldStr schema "x-tazuna-message" with
  | some m =>
    pure { p with issues := p.issues.map fun i => if i.own && !i.authored then { i with message := m } else i }
  | none => pure p

partial def parseNode (schema : Value) (v : Option Value) : ParseM Parsed := do
  match v, schema.field? "default" with
  | none, some d => return { value := some d }
  | _, _ => pure ()
  if schema.field? "x-tazuna-nullable" == some (.bool true) then
    if v == some .null then return { value := v }
    return (← parseValue (nullableInner schema) v).passed
  if let some key := fieldStr schema "x-tazuna-discriminator" then
    if let some options := unionOptions schema then
      return ← parseDiscriminated key options v
  if let some options := optionsOf schema then
    return ← parseUnion options v
  if let some values := allowed schema then
    if v.any fun x => values.any (sameValue x) then return { value := v.map normalized }
    let message := match values with
      | [one] => s!"Invalid input: expected {primitiveText one}"
      | _ => s!"Invalid option: expected one of {"|".intercalate (values.map primitiveText)}"
    return { value := v, issues := [{ fields := [("code", .str "invalid_value"), ("values", .arr values)], message }] }
  let typed ← parseType schema v
  pure (runChecks (checksOf schema) typed)

partial def parseType (schema : Value) (v : Option Value) : ParseM Parsed := do
  let expect (name : String) (ok : Bool) : Parsed :=
    if ok then { value := v.map normalized } else { value := v, issues := [invalidType name v] }
  match fieldStr schema "type", v with
  | some "string", _ => pure (expect "string" (v matches some (.str _)))
  | some "number", _ | some "integer", _ => pure (expect "number" (v matches some (.num _)))
  | some "boolean", _ => pure (expect "boolean" (v matches some (.bool _)))
  | some "null", _ => pure (expect "null" (v matches some .null))
  | some "array", some (.arr xs) =>
    if let some c := (sizeCaps (checksOf schema)).find? (xs.length > ·.2) then
      return { value := v, issues := (runCheck c.1 (.arr xs)).map ({ · with continues := some false }) }
    let item := (schema.field? "items").getD (.obj [])
    let parsed ← xs.mapM fun x => parseValue item (some x)
    pure { value := some (.arr (parsed.map fun p => p.value.getD .null))
           issues := (parsed.zipIdx.map fun (p, i) => p.issues.map (·.under (.num i))).flatten }
  | some "array", _ => pure (expect "array" false)
  | some "object", some (.obj fields) => parseObject schema fields
  | some "object", _ => pure (expect "object" false)
  | _, _ => pure { value := v }

partial def parseObject (schema : Value) (input : List (String × Value)) : ParseM Parsed := do
  let properties := match schema.field? "properties" with
    | some (.obj ps) => ps
    | _ => []
  let required := requiredOf schema
  let mut out : List (String × Value) := []
  let mut issues : List ZodIssue := []
  for (key, p) in properties do
    let present := input.lookup key
    let isRequired := required.contains key
    if present.isNone && !isRequired && p.field? "default" == none then continue
    let r ← parseValue p present
    issues := issues ++ r.issues.map (·.under (.str key))
    if present.isNone && isRequired then
      if r.issues.isEmpty then
        issues := issues ++ [nonoptional key]
      continue
    if let some x := r.value then out := out ++ [(key, x)]
  let extra := input.filter fun (k, _) => (properties.lookup k).isNone
  if !extra.isEmpty then
    let keys := extra.map (·.1)
    issues := issues ++ [checkIssue [("code", .str "unrecognized_keys"), ("keys", .arr (keys.map .str))]
      s!"Unrecognized key{if keys.length > 1 then "s" else ""}: {", ".intercalate (keys.map fun k => "\"" ++ k ++ "\"")}"]
  pure { value := some (.obj out), issues }

/-- A plain union, as Zod's handleUnionResults reads the options' results. -/
partial def parseUnion (options : List Value) (v : Option Value) : ParseM Parsed := do
  match options with
  | [one] => return (← parseValue one v).passed
  | _ =>
    let results ← options.mapM (parseValue · v)
    if let some ok := results.find? (·.issues.isEmpty) then return ok
    match results.filter (!aborted ·.issues) with
    | [one] => pure one.passed
    | _ =>
      pure { value := v, issues := [{ fields := [("code", .str "invalid_union"),
        ("errors", .arr (results.map fun r => .arr (r.issues.map ZodIssue.render)))], message := "Invalid input" }] }

/-- A discriminated union, whose option is the one that the field `key` names. -/
partial def parseDiscriminated (key : String) (options : List Value) (v : Option Value) : ParseM Parsed := do
  let some (.obj fields) := v | return { value := v, issues := [invalidType "object" v] }
  let tag := fields.lookup key
  match options.find? fun o => tag.any fun t => (discriminatorValues key o).any (sameValue t) with
  | some option => return (← parseValue option v).passed
  | none =>
    let values := options.flatMap (discriminatorValues key)
    pure { value := v, issues := [{
      fields := [("code", .str "invalid_union"), ("errors", .arr []), ("note", .str "No matching discriminator"),
        ("discriminator", .str key), ("options", .arr values), ("path", .null)]
      path := [.str key]
      message := s!"Invalid discriminator value. Expected {" | ".intercalate (values.map fun o => "'" ++ scalarText o ++ "'")}" }] }

/-- A value as JS writes it back to JSON: each number in its shortest form. -/
partial def normalized : Value → Value
  | .num n => .num (jsonNumber n)
  | .arr vs => .arr (vs.map normalized)
  | .obj fs => .obj (fs.map fun (k, x) => (k, normalized x))
  | v => v

end

/-- The UTF-16 code units of a string, in whose order JS's `<` compares strings. -/
def utf16 (s : String) : List Nat :=
  s.toList.flatMap fun c =>
    let n := c.toNat
    if n < 0x10000 then [n] else [0xD800 + (n - 0x10000) / 0x400, 0xDC00 + (n - 0x10000) % 0x400]

/-- Whether `a` comes before `b` as JS's `<` orders strings. -/
def jsLess (a b : String) : Bool :=
  let rec go : List Nat → List Nat → Bool
    | [], _ :: _ => true
    | x :: xs, y :: ys => x < y || (x == y && go xs ys)
    | _, _ => false
  go (utf16 a) (utf16 b)

/-- The JSON text of TS's canonicalJson: fields in code point order, numbers as JS writes them. -/
partial def canonicalText : Value → String
  | .num n => jsNumber n
  | .arr vs => arrayText (vs.map canonicalText)
  | .obj fs => objectText (fs.map fun (k, x) => (k, canonicalText x))
  | v => v.canonical

def sortedByText (xs : List Value) : List Value :=
  (xs.map fun x => (x, canonicalText x)).mergeSort (fun a b => !jsLess b.2 a.2) |>.map (·.1)

/-- Adjacent elements whose `key` writes the same JSON, as TS's runsOf groups a sortedBy array. -/
def adjacentRuns (key : String) (xs : List Value) : List (List Value) :=
  let keyText (x : Value) := (x.field? key).map canonicalText
  (xs.foldl (fun (acc : List (List Value)) x =>
    match acc with
    | (y :: ys) :: rest => if keyText y == keyText x then (y :: ys ++ [x]) :: rest else [x] :: (y :: ys) :: rest
    | _ => [x] :: acc) []).reverse

/--
`v` with each bag and set in canonical order and each run of equal keys of a sortedBy array likewise, as TS's bagged
and orderFree read it by `schema`.
-/
partial def orderFree (schema v : Value) : Value :=
  if schema.field? "x-tazuna-nullable" == some (.bool true) then
    if v == .null then v else orderFree (nullableInner schema) v
  else match unionOptions schema with
  | some options =>
    match options.find? (fits · v) with
    | some option => orderFree option v
    | none => v
  | none =>
    match v with
    | .arr xs =>
      let items := match schema.field? "items" with
        | some item => xs.map (orderFree item)
        | none => xs
      match schema.field? "x-tazuna-sorted-by", schema.field? "x-tazuna-bag", schema.field? "x-tazuna-set" with
      | some (.str key), _, _ => .arr ((adjacentRuns key items).flatMap sortedByText)
      | _, some (.bool true), _ | _, _, some (.bool true) => .arr (sortedByText items)
      | _, _, _ => .arr items
    | .obj fields =>
      .obj (fields.map fun (k, x) => (k, match propertyOf schema k with
        | some p => orderFree p x
        | none => x))
    | v => v

/--
`v` as TS's comparable reads it by the object schema `schema`: each field that parses by its own schema encoded again,
with its default where it is absent, and its collections order-free; any other field as it is.
-/
def unorderedBy (schema v : Value) : ParseM Value := do
  let .obj fields := v | return orderFree schema v
  let properties := match schema.field? "properties" with
    | some (.obj ps) => ps
    | _ => []
  let extra := fields.filter fun (k, _) => (properties.lookup k).isNone
  let own ← properties.filterMapM fun (k, p) => do
    let given := fields.lookup k
    let r ← parseValue p given
    if !r.issues.isEmpty then return given.map (k, ·)
    pure (r.value.map (k, ·))
  pure (orderFree schema (.obj (own ++ extra)))

/--
The text of an answer as verify compares a query's answers, as TS's comparableAnswer and canonicalJson write it: a
rejection by its kind, and an output read by `output`, its query's output schema, as unorderedBy reads it.
-/
def comparableText (output : Option Value) (answer : Value) : ParseM Value := do
  let compared ← match answer.field? "result", answer.field? "output", output with
    | some (.str "rejected"), _, _ =>
      pure (.obj [("result", .str "rejected"),
        ("rejection", .obj (((answer.field? "rejection").bind (·.field? "kind")).toList.map ("kind", ·)))])
    | _, some o, some schema => do pure (answer.merge (.obj [("output", ← unorderedBy schema o)]))
    | _, _, _ => pure answer
  pure (.str (canonicalText compared))

/-- The default of each field of the object schema `schema` that declares one, in its order. -/
def defaultsOf (schema : Value) : Value :=
  match schema.field? "properties" with
  | some (.obj ps) => .obj (ps.filterMap fun (k, p) => (p.field? "default").map (k, ·))
  | _ => .obj []

/-- The JSON Schema that TS parses with for a definition's schema: an object with no fields when it names none. -/
def rootSchema (schema : Value) : Value :=
  if schema == .obj [] then .obj [("type", .str "object"), ("properties", .obj []), ("additionalProperties", .bool false)]
  else schema

/--
`v` parsed by `schema` as TS's parse does: the value encoded again, or Zod's issues as it renders them, or a throw. None
when `schema` says less than Zod checks.
-/
def parse (schema v : Value) : Option (ParseM (Except (List Value) Value)) :=
  let root := rootSchema schema
  if !supported root then none else
  some do
    let p ← parseValue root (some v)
    pure (if p.issues.isEmpty then .ok (p.value.getD .null) else .error (p.issues.map ZodIssue.render))

end Tazuna.Data
