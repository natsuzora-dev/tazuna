import Tazuna.Data.Binary64
import Tazuna.Data.Time
import Tazuna.Data.UnionOptions

/-!
Parsing a value by its JSON Schema as Zod's safeParse does, for the schemas whose JSON Schema says all that Zod checks
(`supported`): the value that the parse gives, encoded again as JSON, or the issues that Zod reports, field for field
and in Zod's order. TS writes what JSON Schema leaves out as `x-tazuna-*` keywords: the checks in Zod's order, a
nullable, a discriminator, a tazuna time codec, and `x-tazuna-opaque` where only Zod knows what happens.
-/

namespace Tazuna.Data

/--
An issue as Zod reports it: its fields in Zod's order, where `path` and `message` sit only when Zod made the issue
with them, then its path and its message. `continues` is the issue's `continue`, which tells whether later checks run.
-/
structure ZodIssue where
  fields : List (String × Value)
  path : List Value := []
  message : String
  continues : Option Bool := none
deriving Inhabited

def ZodIssue.under (key : Value) (i : ZodIssue) : ZodIssue := { i with path := key :: i.path }

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

/-- Whether a check without a `when` is skipped, as Zod's util.aborted: an issue that does not say it continues. -/
def aborted (issues : List ZodIssue) : Bool := issues.any (·.continues != some true)

/-- Whether even a check with a `when` is skipped, as Zod's util.explicitlyAborted: an issue that says it stops. -/
def explicitlyAborted (issues : List ZodIssue) : Bool := issues.any (·.continues == some false)

/-- An author's code or a codec's transform threw, as a refinement of Temporal's does on a fraction past nanoseconds. -/
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

/-- The text of `n`, `width` digits wide. -/
def digits (width : Nat) (n : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-- Zod's pattern of z.iso.datetime({ offset: true }), z.iso.date() and z.iso.duration(), as an issue writes it. -/
def datePattern : String :=
  "(?:(?:\\d\\d[2468][048]|\\d\\d[13579][26]|\\d\\d0[48]|[02468][048]00|[13579][26]00)-02-29|\\d{4}-(?:(?:0[13578]|1[02])-(?:0[1-9]|[12]\\d|3[01])|(?:0[469]|11)-(?:0[1-9]|[12]\\d|30)|(?:02)-(?:0[1-9]|1\\d|2[0-8])))"

def formatPattern : String → String
  | "datetime" => "/^" ++ datePattern ++
      "T(?:(?:[01]\\d|2[0-3]):[0-5]\\d:[0-5]\\d(?:\\.\\d+)?(?:Z|([+-](?:[01]\\d|2[0-3]):[0-5]\\d)))$/"
  | "date" => "/^" ++ datePattern ++ "$/"
  | _ => "/^P(?:(\\d+W)|(?!.*W)(?=\\d|T\\d)(\\d+Y)?(\\d+M)?(\\d+D)?(T(?=\\d)(\\d+H)?(\\d+M)?(\\d+([.,]\\d+)?S)?)?)$/"

def formatName : String → String
  | "datetime" => "ISO datetime"
  | "date" => "ISO date"
  | _ => "ISO duration"

/-- Whether z.iso.date() accepts `text`. -/
def isDate (text : String) : Bool := isOffsetDateTime (text ++ "T00:00:00Z") && text.length == 10

/-- The parts of a duration that z.iso.duration() accepts: each unit's digits, and the seconds' fraction digits. -/
structure DurationParts where
  units : List (Char × Nat) := []
  fraction : List Char := []

/-- Digits at the head of `cs`, and what follows them. -/
def leadingNumber (cs : List Char) : Option (Nat × List Char) :=
  let ds := cs.takeWhile Char.isDigit
  if ds.isEmpty then none else some ((String.ofList ds).toNat!, cs.drop ds.length)

/-- The units at the head of `cs` that come in the order of `allowed`, each once, and what follows them. -/
def durationUnits (allowed : List Char) (cs : List Char) : List (Char × Nat) × List Char :=
  match allowed with
  | [] => ([], cs)
  | u :: later =>
    match leadingNumber cs with
    | some (n, c :: rest) =>
      if c == u then
        let (more, after) := durationUnits later rest
        ((u, n) :: more, after)
      else durationUnits later cs
    | _ => ([], cs)

/-- The parts of `text` when z.iso.duration() accepts it. -/
def durationParts? (text : String) : Option DurationParts := do
  let cs := text.toList
  guard (cs.head? == some 'P')
  let number := leadingNumber
  let body := cs.drop 1
  match number body with
  | some (n, ['W']) => pure { units := [('W', n)] }
  | _ =>
    let (date, rest) := durationUnits ['Y', 'M', 'D'] body
    match rest with
    | [] => if date.isEmpty then none else pure { units := date }
    | 'T' :: time =>
      let (hm, rest) := durationUnits ['H', 'M'] time
      let (seconds, fraction, rest) ← match number rest with
        | some (s, sep :: more) =>
          if sep == 'S' then some ([('S', s)], [], more)
          else if sep == '.' || sep == ',' then
            let f := more.takeWhile Char.isDigit
            if !f.isEmpty && more.drop f.length == ['S'] then some ([('S', s)], f, []) else none
          else none
        | _ => some ([], [], rest)
      guard (rest.isEmpty && !(hm ++ seconds).isEmpty)
      pure { units := date ++ [('T', 0)] ++ hm ++ seconds, fraction }
    | _ => none

/-- The text of `Temporal.Duration.from(text).toString()`, or a throw where Temporal rejects the duration. -/
def durationText (p : DurationParts) : ParseM String := do
  if p.fraction.length > 9 then throw ()
  let unit (u : Char) (after : Bool) : Nat :=
    let afterT := p.units.dropWhile (·.1 != 'T')
    ((if after then afterT else p.units.takeWhile (·.1 != 'T')).lookup u).getD 0
  let (years, months, weeks, days) := (unit 'Y' false, unit 'M' false, unit 'W' false, unit 'D' false)
  let (hours, minutes, seconds) := (unit 'H' true, unit 'M' true, unit 'S' true)
  if years ≥ 2 ^ 32 || months ≥ 2 ^ 32 || weeks ≥ 2 ^ 32 then throw ()
  if days * 86400 + hours * 3600 + minutes * 60 + seconds ≥ 2 ^ 53 then throw ()
  let fraction := String.ofList ((p.fraction.reverse.dropWhile (· == '0')).reverse)
  let part (n : Nat) (u : String) := if n == 0 then "" else toString n ++ u
  let date := part years "Y" ++ part months "M" ++ part weeks "W" ++ part days "D"
  let secondsText := if seconds == 0 && fraction.isEmpty then "" else
    toString seconds ++ (if fraction.isEmpty then "" else "." ++ fraction) ++ "S"
  let time := part hours "H" ++ part minutes "M" ++ secondsText
  pure (if date.isEmpty && time.isEmpty then "PT0S" else "P" ++ date ++ (if time.isEmpty then "" else "T" ++ time))

/-- The text of `Temporal.Instant.from(text).toString()` for a text that z.iso.datetime({ offset: true }) accepts. -/
def instantText (text : String) : ParseM String := do
  let cs := text.toList
  let fraction := if cs[19]? == some '.' then (cs.drop 20).takeWhile Char.isDigit else []
  if fraction.length > 9 then throw ()
  let num (a b : Nat) : Int := (String.ofList ((cs.drop a).take (b - a))).toNat!
  let rest := cs.drop (19 + (if fraction.isEmpty then 0 else fraction.length + 1))
  let offset : Int := match rest with
    | [sign, a, b, ':', c, d] =>
      let m := (String.ofList [a, b]).toNat! * 60 + (String.ofList [c, d]).toNat!
      if sign == '-' then -m else m
    | _ => 0
  let nanos : Int := (String.ofList ((fraction ++ List.replicate 9 '0').take 9)).toNat!
  let seconds := (((daysFromCivil (num 0 4) (num 5 7) (num 8 10) * 24 + num 11 13) * 60 + num 14 16 - offset) * 60 +
    num 17 19)
  let days := seconds / 86400
  let daySeconds := (seconds % 86400).toNat
  let (y, mo, d) := civilFromDays days
  let year := if 0 ≤ y && y ≤ 9999 then digits 4 y.toNat else (if y < 0 then "-" else "+") ++ digits 6 y.natAbs
  let subsecond := String.ofList ((digits 9 nanos.toNat).toList.reverse.dropWhile (· == '0')).reverse
  pure (s!"{year}-{digits 2 mo.toNat}-{digits 2 d.toNat}T{digits 2 (daySeconds / 3600)}:" ++
    s!"{digits 2 (daySeconds / 60 % 60)}:{digits 2 (daySeconds % 60)}" ++
    (if subsecond.isEmpty then "" else "." ++ subsecond) ++ "Z")

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
    | some "datetime" =>
      c.field? "offset" == some (.bool true) && c.field? "local" == some (.bool false) &&
        c.field? "precision" == some .null
    | some "date" | some "duration" => true
    | _ => false
  | _ => false

/-- The keywords that parse reads or that change nothing that Zod checks. -/
def knownKeywords : List String :=
  ["$schema", "type", "properties", "required", "additionalProperties", "items", "minItems", "maxItems", "minLength",
   "maxLength", "minimum", "maximum", "exclusiveMinimum", "exclusiveMaximum", "multipleOf", "format", "pattern",
   "enum", "const", "anyOf", "oneOf", "default", "uniqueItems", "description", "title", "examples",
   "x-tazuna-checks", "x-tazuna-nullable", "x-tazuna-discriminator", "x-tazuna-time", "x-tazuna-bag",
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
    fields.all (fun (k, v) =>
      knownKeywords.contains k || (k == "allOf" && patternsOnly v) ||
      -- A duration is a codec to a sort key, since its text does not order as its length does.
      (k == "x-tazuna-codec" && schema.field? "x-tazuna-time" == some (.str "duration"))) &&
    (checksOf schema).all supportedCheck &&
    (match schema.field? "x-tazuna-time" with
      | none | some (.str "instant") | some (.str "date") | some (.str "duration") => true
      | _ => false) &&
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
def runCheck (c : Value) (v : Value) : List ZodIssue :=
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
      let ok := match format with
        | "datetime" => isOffsetDateTime s
        | "date" => isDate s
        | _ => (durationParts? s).isSome
      if ok then [] else
      [checkIssue [("origin", .str "string"), ("code", .str "invalid_format"), ("format", .str format),
        ("pattern", .str (formatPattern format))] s!"Invalid {formatName format}"]
  | some "set", .arr vs =>
    let (_, issues) := vs.zipIdx.foldl (fun ((seen : List String), (issues : List ZodIssue)) (x, i) =>
      let text := x.canonical
      (seen ++ [text], if seen.contains text then
        issues ++ [{ fields := [("code", .str "custom"), ("message", .str ""), ("path", .null)], path := [.num i]
                     message := s!"duplicate element {text}" }]
       else issues)) ([], [])
    issues
  | _, _ => []

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

/-- The value of the time codec `kind` for a text that its format took, as the codec decodes and encodes it. -/
def timeValue (kind : String) (s : String) : ParseM Value :=
  match kind with
  | "instant" => do pure (.str (← instantText s))
  | "duration" =>
    match durationParts? s with
    | some p => do pure (.str (← durationText p))
    | none => pure (.str s)
  | _ => pure (.str s)

/-- The discriminator values of an option: its field's `const` or `enum`. -/
def discriminatorValues (key : String) (option : Value) : List Value :=
  match propertyOf option key with
  | some p => (allowed p).getD []
  | none => []

mutual

/-- `v` parsed by `schema` as Zod's safeParse does. -/
partial def parseValue (schema : Value) (v : Option Value) : ParseM Parsed := do
  match v, schema.field? "default" with
  | none, some d => return { value := some d }
  | _, _ => pure ()
  if schema.field? "x-tazuna-nullable" == some (.bool true) then
    if v == some .null then return { value := v }
    return ← parseValue (nullableInner schema) v
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
  let checked := runChecks (checksOf schema) typed
  match fieldStr schema "x-tazuna-time", checked.value with
  | some kind, some (.str s) =>
    if checked.issues.isEmpty then pure { value := some (← timeValue kind s) } else pure checked
  | _, _ => pure checked

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
  | [one] => parseValue one v
  | _ =>
    let results ← options.mapM (parseValue · v)
    if let some ok := results.find? (·.issues.isEmpty) then return ok
    match results.filter (!aborted ·.issues) with
    | [one] => pure one
    | _ =>
      pure { value := v, issues := [{ fields := [("code", .str "invalid_union"),
        ("errors", .arr (results.map fun r => .arr (r.issues.map ZodIssue.render)))], message := "Invalid input" }] }

/-- A discriminated union, whose option is the one that the field `key` names. -/
partial def parseDiscriminated (key : String) (options : List Value) (v : Option Value) : ParseM Parsed := do
  let some (.obj fields) := v | return { value := v, issues := [invalidType "object" v] }
  let tag := fields.lookup key
  match options.find? fun o => tag.any fun t => (discriminatorValues key o).any (sameValue t) with
  | some option => parseValue option v
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
