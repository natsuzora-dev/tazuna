import Tazuna.Scenario.Given
import Tazuna.Service.Functions

/-!
The values that explore writes into the lines it appends: those the spec's scenarios already write, then representative
values of each schema. A value that its schema's refinements reject is dropped by asking Functions.parse.
-/

namespace Tazuna.Explore

open Tazuna.Data Tazuna.Service

/-- The values that one definition, or one control of a screen, receives in the scenarios, in written order. -/
structure Written (α : Type) where
  of : α
  values : List Value
deriving Repr, Inhabited

/--
What the scenarios of a spec write, tried first: the strings anywhere in a written value (`words`), the answers of
external peers by request target, the inputs of requests and payloads of events by definition, and the payloads of
operations by screen and control.
-/
structure Seen where
  words : List String := []
  answers : List (Written Spec.Ref) := []
  messages : List (Written Spec.Ref) := []
  payloads : List (Written (Spec.Ref × String)) := []
deriving Repr, Inhabited

def Written.add {α : Type} [BEq α] (ws : List (Written α)) (a : α) (v : Value) : List (Written α) :=
  if ws.any (·.of == a) then ws.map fun w => if w.of == a then { w with values := w.values ++ [v] } else w
  else ws ++ [{ of := a, values := [v] }]

def Written.lookup {α : Type} [BEq α] (ws : List (Written α)) (a : α) : List Value :=
  ((ws.find? (·.of == a)).map (·.values)).getD []

def Seen.add (s : Seen) (v : Value) : Seen :=
  { s with words := v.strings.foldl (fun ws w => if ws.contains w then ws else ws ++ [w]) s.words }

/-- What the lines of `scenarios` write, in scenario and line order. -/
def seenOf (scenarios : List Scenario) : Seen :=
  scenarios.foldl (init := {}) fun s sc => sc.lines.foldl (init := s) fun s l =>
    match l with
    | .request _ _ target input _ => { s.add input.value with messages := Written.add s.messages target input.value }
    | .emit _ event payload _ => { s.add payload.value with messages := Written.add s.messages event payload.value }
    | .answer _ (.request _ _ target _) a => { s.add a.value with answers := Written.add s.answers target a.value }
    | .operate (.screen _ screen) control payload =>
      { s.add payload.value with payloads := Written.add s.payloads (screen, control) payload.value }
    | _ => s

/-- The strings a representative string is chosen from, after the scenario's words. -/
def fillerStrings : List String := ["a", "b", "c"]

/-- The numbers a representative number is chosen from. -/
def representativeNumbers : List Lean.JsonNumber := [0, 1, 2, -1, ⟨5, 1⟩, 10, 1000]

def representativeDates : List String := ["2026-10-25", "2026-10-26"]

def representativeDateTimes : List String := ["2026-10-25T00:00:00Z", "2026-10-26T00:00:00Z"]

/-- Whether `a / b` is an integer. -/
def multipleOf (a b : Lean.JsonNumber) : Bool :=
  b.mantissa != 0 && (a.mantissa * 10 ^ b.exponent) % (b.mantissa * 10 ^ a.exponent) == 0

/-- Whether `a < b`, exactly: Lean.JsonNumber.lt takes 0 as less than every negative number. -/
def lessThan (a b : Lean.JsonNumber) : Bool := a.mantissa * 10 ^ b.exponent < b.mantissa * 10 ^ a.exponent

/-- Whether the number `n` meets the bounds of the JSON Schema `s`, and is an integer when `integer`. -/
def numberFits (s : Value) (integer : Bool) (n : Lean.JsonNumber) : Bool :=
  let bound (key : String) (holds : Lean.JsonNumber → Bool) := match s.field? key with
    | some (.num b) => holds b
    | _ => true
  (!integer || multipleOf n 1) && bound "minimum" (fun b => !lessThan n b) && bound "maximum" (fun b => !lessThan b n) &&
    bound "exclusiveMinimum" (fun b => lessThan b n) && bound "exclusiveMaximum" (fun b => lessThan n b) &&
    bound "multipleOf" (multipleOf n)

/-- Whether the string `x` meets the length bounds of the JSON Schema `s`, in code points. -/
def stringFits (s : Value) (x : String) : Bool :=
  let bound (key : String) (holds : Nat → Bool) := match s.field? key with
    | some (.num b) => holds b.mantissa.toNat
    | _ => true
  bound "minLength" (x.length ≥ ·) && bound "maxLength" (x.length ≤ ·)

def pick? {α : Type} (xs : List α) (i : Nat) : Option α := if xs.isEmpty then none else xs[i % xs.length]?

/--
The `i`th representative value of the JSON Schema `s`, or none when `s` has no type it can choose for. A union, a
type list, an enum and a boolean alternate with `i`; a string comes from `words` and then fillerStrings; an array is
empty at 0 and holds one element after; an object holds every property. A sortedBy array stays empty, since one element
of it may not be what its key orders. Only the keywords the structure states are read, so a value that a refinement
rejects is dropped by valuesFor.
-/
partial def representative (words : List String) (s : Value) (i : Nat) : Option Value :=
  match s.field? "anyOf", s.field? "oneOf", s.field? "const", s.field? "enum", s.field? "type" with
  | some (.arr options), _, _, _, _ | none, some (.arr options), _, _, _ =>
    (pick? options i).bind (representative words · i)
  | none, none, some c, _, _ => some c
  | none, none, none, some (.arr values), _ => pick? values i
  | none, none, none, _, some (.arr types) =>
    (pick? types i).bind fun t => representative words (overlay s t) i
  | none, none, none, _, some (.str t) => typed t
  | _, _, _, _, _ => none
where
  overlay (s t : Value) : Value := match s with
    | .obj fields => .obj (fields.map fun (k, v) => (k, if k == "type" then t else v))
    | _ => s
  typed : String → Option Value
    | "null" => some .null
    | "boolean" => some (.bool (i % 2 == 1))
    | "string" => match s.field? "format" with
      | some (.str "date-time") => (pick? representativeDateTimes i).map .str
      | some (.str "date") => (pick? representativeDates i).map .str
      | _ => (pick? ((words ++ fillerStrings).filter (stringFits s)) i).map .str
    | "number" => (pick? (representativeNumbers.filter (numberFits s false)) i).map .num
    | "integer" => (pick? (representativeNumbers.filter (numberFits s true)) i).map .num
    | "array" =>
      if i == 0 || (s.field? "x-tazuna-sorted-by").isSome then some (.arr []) else
      some (.arr ((s.field? "items").bind (representative words · (i - 1))).toList)
    | "object" => match s.field? "properties" with
      | some (.obj properties) =>
        (properties.mapM fun (kp : String × Value) => (representative words kp.2 i).map (kp.1, ·)).map .obj
      | _ => some (.obj [])
    | _ => none

/-- `values` without a value whose canonical text an earlier one has. -/
def distinct (values : List Value) : List Value :=
  values.foldl (fun kept v => if kept.any (·.canonical == v.canonical) then kept else kept ++ [v]) []

variable {m : Type → Type} [Monad m] [MonadNote m]

/--
Up to `n` values of the schema `schema`: the `listed` ones first, then representative values 0 to `n + 1` that
parseOutside accepts, stopping once `n` are found. A refinement that throws is the schema owner's fault.
-/
def valuesFor (st : Service) (fs : Functions m) (schema : Schema) (listed : List Value) (words : List String) (n : Nat) :
    m (Except Fault (List Value)) := do
  let json ← expectFound s!"schema {repr schema}" (st.schemaOf schema)
  let found ← (List.range (n + 2)).foldlM (init := (.ok (distinct listed) : Except Fault (List Value))) fun acc i => do
    match acc with
    | .error f => pure (.error f)
    | .ok found =>
      if found.length ≥ n then pure (.ok found) else
      match representative words json i with
      | none => pure (.ok found)
      | some v => match ← fs.parseOutside st schema v with
        | .error issue => pure (.error (issueViolation schema.owner issue))
        | .ok none => pure (.ok found)
        | .ok (some _) => pure (.ok (distinct (found ++ [v])))
  pure (found.map (·.take n))

end Tazuna.Explore
