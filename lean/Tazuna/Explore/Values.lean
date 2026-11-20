import Tazuna.Scenario.Given
import Tazuna.Service.Functions

/-!
The values that explore writes into the lines it appends: those the spec's scenarios already write, then representative
values of each schema. Functions.fits picks each leaf's candidates by that leaf's own refinements, and Functions.parse
drops a value that the refinements of the whole reject.
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

def pick? {α : Type} (xs : List α) (i : Nat) : Option α := if xs.isEmpty then none else xs[i % xs.length]?

variable {m : Type → Type} [Monad m] [MonadNote m]

/--
The `i`th of the `candidates` that `fits` takes, counted cyclically, or none when it takes none. It asks only until it
finds the `i`th, so a leaf without a refinement costs `i + 1` questions.
-/
def fitting (fits : Value → m (Except Issue Bool)) (candidates : List Value) (i : Nat) : ExceptT Issue m (Option Value) :=
  go candidates []
where
  go : List Value → List Value → ExceptT Issue m (Option Value)
    | [], found => pure (pick? found i)
    | c :: cs, found => do
      if ← ExceptT.mk (fits c) then
        if found.length == i then pure (some c) else go cs (found ++ [c])
      else go cs found

/--
The `i`th representative value of the JSON Schema `s`, at `path` in the schema that `fits` reads, or none when `s` has
no type it can choose for. A union, a type list, an enum and a boolean alternate with `i`. A string comes from `words`
and then fillerStrings, and a number from representativeNumbers, each the `i`th of those that `fits` takes at its own
path, so that one leaf's refinements never reject the value of another. An array is empty at 0 and holds one element
after; an object holds every property, each at index `i`. A sortedBy array stays empty, since one element of it may not
be what its key orders.
-/
partial def representative (fits : List SchemaStep → Value → m (Except Issue Bool)) (words : List String)
    (s : Value) (path : List SchemaStep) (i : Nat) : ExceptT Issue m (Option Value) :=
  match s.field? "anyOf", s.field? "oneOf", s.field? "const", s.field? "enum", s.field? "type" with
  | some (.arr options), _, _, _, _ | none, some (.arr options), _, _, _ => option options id
  | none, none, some c, _, _ => pure (some c)
  | none, none, none, some (.arr values), _ => pure (pick? values i)
  | none, none, none, _, some (.arr types) => option types (overlay s)
  | none, none, none, _, some (.str t) => typed t
  | _, _, _, _, _ => pure none
where
  overlay (s t : Value) : Value := match s with
    | .obj fields => .obj (fields.map fun (k, v) => (k, if k == "type" then t else v))
    | _ => s
  option (options : List Value) (schemaOf : Value → Value) : ExceptT Issue m (Option Value) :=
    match pick? options.zipIdx i with
    | some (o, j) => representative fits words (schemaOf o) (path ++ [.option j]) i
    | none => pure none
  typed : String → ExceptT Issue m (Option Value)
    | "null" => pure (some .null)
    | "boolean" => pure (some (.bool (i % 2 == 1)))
    | "string" => match s.field? "format" with
      | some (.str "date-time") => pure ((pick? representativeDateTimes i).map .str)
      | some (.str "date") => pure ((pick? representativeDates i).map .str)
      | _ => fitting (fits path) ((words ++ fillerStrings).map .str) i
    | "number" | "integer" => fitting (fits path) (representativeNumbers.map .num) i
    | "array" =>
      if i == 0 || (s.field? "x-tazuna-sorted-by").isSome then pure (some (.arr [])) else
      match s.field? "items" with
      | some items => do pure (some (.arr (← representative fits words items (path ++ [.items]) (i - 1)).toList))
      | none => pure (some (.arr []))
    | "object" => match s.field? "properties" with
      | some (.obj properties) => do
        let values ← properties.mapM fun (k, p) => do
          pure ((← representative fits words p (path ++ [.field k]) i).map (k, ·))
        pure ((values.mapM id).map .obj)
      | _ => pure (some (.obj []))
    | _ => pure none

/-- `values` without a value whose canonical text an earlier one has. -/
def distinct (values : List Value) : List Value :=
  values.foldl (fun kept v => if kept.any (·.canonical == v.canonical) then kept else kept ++ [v]) []

/--
Up to `n` values of the schema `schema`: the `listed` ones first, then the representative values at indices 0 to
`n + 1` that parseOutside accepts. A value already found is not parsed again. A refinement that throws is the schema
owner's fault.
-/
def valuesFor (st : Service) (fs : Functions m) (schema : Schema) (listed : List Value) (words : List String) (n : Nat) :
    m (Except Fault (List Value)) := do
  let json ← expectFound s!"schema {repr schema}" (st.schemaOf schema)
  let found ← (List.range (n + 2)).foldlM (init := (.ok (distinct listed) : Except Fault (List Value))) fun acc i => do
    match acc with
    | .error f => pure (.error f)
    | .ok found =>
      if found.length ≥ n then pure (.ok found) else
      match ← (representative (fs.fits schema) words json [] i).run with
      | .error issue => pure (.error (issueViolation schema.owner issue))
      | .ok none => pure (.ok found)
      | .ok (some v) =>
        if found.any (·.canonical == v.canonical) then pure (.ok found) else
        match ← fs.parseOutside st schema v with
        | .error issue => pure (.error (issueViolation schema.owner issue))
        | .ok none => pure (.ok found)
        | .ok (some _) => pure (.ok (found ++ [v]))
  pure (found.map (·.take n))

end Tazuna.Explore
