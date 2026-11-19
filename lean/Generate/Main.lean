import Lean.Elab.Term
import Tazuna.Data.Names
import Tazuna.Service.Limits
import Tazuna.Data.Trace
import Tazuna.Explore.ChoiceDependent
import Tazuna.Explore.BagOrderDependent
import Tazuna.Service.Fault
import Tazuna.Service.InvalidInput
import Tazuna.Service.Note
import Tazuna.Spec.Structure
import Tazuna.Scenario.Given
import Tazuna.Sim.InvalidScenario
import Tazuna.Validation.Illegal
import Tazuna.Verify.Mismatch
import Tazuna.Verify.Uncomparable
import DiffTest.Protocol

/-!
The text is laid out as Biome formats it, since `npm run lint` checks it.

A violation type and a wire type (Data/Wire.lean) differ in two ways. A violation's `Option` field is always `T | null`,
and a wire type's is an optional property under skip_serializing_none. A violation's constructor is
named by its `kind` (`"Group.constructor"`), and a wire type's constructor by its `tag` field, whose value is the
constructor's name, kebab-case under rename_all.
-/

open Lean Elab Term Meta Tazuna.Data

/--
The TS constant `name`: the strings `values` as a const array, on one line when it fits in 120 columns and one string
per line otherwise, as Biome formats it.
-/
def constArray (name : String) (values : List String) : String :=
  let quoted := values.map fun v => s!"\"{v}\""
  let oneLine := s!"export const {name} = [{", ".intercalate quoted}] as const;"
  if oneLine.length ≤ 120 then oneLine ++ "\n"
  else s!"export const {name} = [\n" ++ String.join (quoted.map fun q => s!"  {q},\n") ++ "] as const;\n"

/-- The TS type of each Lean type that no generated file declares: a TS built-in, or a type of a hand-written module. -/
def handTypes : List (Name × String × Option String) :=
  [(``String, "string", none), (``Nat, "number", none), (``Bool, "boolean", none), (``Tazuna.Data.Time, "string", none),
   (``Tazuna.Data.DateTime, "string", none), (``Tazuna.Data.Value, "Json", some "src/data/values.ts"),
   (``Tazuna.Spec.Ref, "DefinitionRef", some "src/data/definitionRef.ts"),
   (``Tazuna.Data.Violation, "ViolationValue", some "src/data/violation.ts"),
   (``Tazuna.Verify.At, "At", some "src/verify/pairing.ts"),
   (``Tazuna.Verify.Run, "Run", some "src/data/traceFile.ts"),
   (``Tazuna.Verify.Expected, "Expected", some "src/verify/pairing.ts"),
   (``Tazuna.Verify.Folder, "Folder", some "src/verify/pairing.ts")]

/-- The Lean sums whose constructors each wrap one value and write it as it is, with the types that they wrap. -/
def sums : List (Name × List Name) :=
  [(``Tazuna.Verify.Finding, [``Tazuna.Verify.Mismatch, ``Tazuna.Verify.Uncomparable])]

/-- Each generated module, by repository path, and the Lean types that it declares, the root last. -/
def modules : List (String × List Name) :=
  [("src/data/illegal.generated.ts", [``Tazuna.Validation.Illegal]),
   ("src/data/mismatch.generated.ts", [``Tazuna.Verify.Subject, ``Tazuna.Verify.Mismatch]),
   ("src/data/uncomparable.generated.ts", [``Tazuna.Verify.Uncomparable]),
   ("src/data/invalidInput.generated.ts", [``Tazuna.Service.InvalidInput]),
   ("src/data/invalidScenario.generated.ts", [``Tazuna.Sim.InvalidScenario]),
   ("src/data/scenario.generated.ts",
    [``Tazuna.Spec.Ref, ``Tazuna.Scenario.Origin, ``Tazuna.Scenario.Fact, ``Tazuna.Scenario.ValueRef,
     ``Tazuna.Scenario.Fill, ``Tazuna.Scenario.Hole, ``Tazuna.Scenario.Template, ``Tazuna.Scenario.Line,
     ``Tazuna.Scenario.SentRequest, ``Tazuna.Scenario.EmittedEvent, ``Tazuna.Scenario.Expectation,
     ``Tazuna.Scenario.GivenRecord, ``Tazuna.Scenario.Peer, ``Tazuna.Scenario.PeerEntry, ``Tazuna.Scenario.Given,
     ``Tazuna.Scenario]),
   ("src/data/fault.generated.ts", [``Tazuna.Service.Fault]),
   ("src/data/bagOrderDependent.generated.ts", [``Tazuna.Explore.BagOrderDependent]),
   ("src/data/choiceDependent.generated.ts",
    [``Tazuna.Explore.Difference, ``Tazuna.Explore.ChoiceDependent]),
   ("src/data/transitionRef.generated.ts",
    [``Tazuna.Spec.CallOutcome, ``Tazuna.Spec.SendOutcome, ``Tazuna.Spec.Trigger, ``Tazuna.Spec.TransitionRef]),
   ("src/data/step.generated.ts",
    [``Tazuna.Service.InstanceId, ``Tazuna.Service.Requester, ``Tazuna.Service.Received, ``Tazuna.Service.Activity,
     ``Tazuna.Service.StepName]),
   ("src/data/trace.generated.ts",
    [``Tazuna.Data.RejectionKind, ``Tazuna.Data.Rejection, ``Tazuna.Data.Answer, ``Tazuna.Data.LineId,
     ``Tazuna.Data.TraceLine]),
   ("src/spec/structure.generated.ts",
    [``Tazuna.Spec.Activity, ``Tazuna.Spec.Transition, ``Tazuna.Spec.State, ``Tazuna.Spec.ChartFields,
     ``Tazuna.Spec.Reference, ``Tazuna.Spec.KeyPosition, ``Tazuna.Spec.Body, ``Tazuna.Spec.Definition, ``Tazuna.Spec.Contract,
     ``Tazuna.Spec.ServiceInfo, ``Tazuna.Spec.ResultOfMismatch, ``Tazuna.Spec.AssumptionMismatch,
     ``Tazuna.Spec.Structure]),
   ("test/lean/protocol.generated.ts",
    [``Tazuna.Service.Schema, ``Tazuna.Service.Issue, ``Tazuna.Service.CopyScope, ``Tazuna.Service.Scope,
     ``Tazuna.Service.Transition, ``Tazuna.Service.Assignment, ``Tazuna.Service.Edge, ``Tazuna.Service.Extra, ``Tazuna.Service.Emit,
     ``Tazuna.Service.NextKeys, ``Tazuna.Service.Keys, ``Tazuna.Explore.Holder, ``Tazuna.Explore.Access,
     ``Tazuna.Verify.Part, ``Tazuna.Service.Operation, ``Tazuna.Explore.Awaiting, ``Tazuna.Explore.Enabled,
     ``Tazuna.DiffTest.PairedService, ``Tazuna.DiffTest.StepOrder,
     ``Tazuna.DiffTest.Request, ``Tazuna.DiffTest.Question, ``Tazuna.DiffTest.Asked, ``Tazuna.DiffTest.ItemKey,
     ``Tazuna.DiffTest.Reply, ``Tazuna.DiffTest.Replied, ``Tazuna.DiffTest.Unpaired,
     ``Tazuna.DiffTest.SimulatedService, ``Tazuna.DiffTest.TriedOrder, ``Tazuna.DiffTest.SearchedProcessing,
     ``Tazuna.DiffTest.Response])]

def declaredIn (path : String) : MetaM (List Name) := do
  let some types := modules.lookup path | throwError "modules has no {path}"
  pure types

/-- The path of the file `target` as an import in the file `file`, both relative to the repository. -/
def relativePath (file target : String) : String :=
  let dir := (file.splitOn "/").dropLast
  let parts := target.splitOn "/"
  let common := ((dir.zip parts).takeWhile fun (a, b) => a == b).length
  let rest := "/".intercalate (parts.drop common)
  if dir.length == common then "./" ++ rest else String.join (List.replicate (dir.length - common) "../") ++ rest

/-- The state of writing a generated module: its path, the types that it declares, and the types that it imports. -/
structure Writing where
  file : String
  declared : List Name
  imports : List (String × String) := []

abbrev Write := StateT Writing MetaM

/-- The TS name of the Lean type `name`, which the module imports unless it declares it. -/
partial def named (name : Name) : Write String := do
  let importing (ts path : String) : Write Unit :=
    modify fun w => if (ts, path) ∈ w.imports then w else { w with imports := w.imports ++ [(ts, path)] }
  if let some (_, ts, path) := handTypes.find? (·.1 == name) then
    if let some path := path then importing ts path
    return ts
  if let some (_, members) := sums.find? (·.1 == name) then
    return " | ".intercalate (← members.mapM named)
  let ts := name.getString!
  if (← get).declared.contains name then return ts
  if let some (path, _) := modules.find? (·.2.contains name) then
    importing ts path
    return ts
  if let .enum ctors ← wireShape name then
    return " | ".intercalate (ctors.map fun c => s!"\"{c.name}\"")
  throwError "no generated module declares {name}; add it to modules"

/-- The TS type of a Lean type. -/
partial def tsType : Expr → Write String
  | .app (.const ``Option _) a => return s!"{← tsType a} | null"
  | .app (.const ``List _) (.app (.app (.const ``Prod _) (.const ``String _)) a) =>
    return s!"Readonly<Record<string, {← tsType a}>>"
  | .app (.const ``List _) a => do
    let t ← tsType a
    return if t.startsWith "readonly " || (t.splitOn " | ").length > 1 then s!"readonly ({t})[]" else s!"readonly {t}[]"
  | .app (.app (.const ``Prod _) a) b => return s!"readonly [{← tsType a}, {← tsType b}]"
  | .app (.const ``Tazuna.Data.FileLine _) a => return s!"null | \"malformed\" | {← tsType a}"
  | .const name _ => named name
  | type => throwError "no TS type for {type}"

def jsdoc (indent doc : String) : String :=
  match (doc.trimAscii.toString.splitOn "\n").map (·.trimAsciiStart.toString) with
  | [line] => s!"{indent}/** {line} */\n"
  | lines =>
    s!"{indent}/**\n" ++
      String.join (lines.map fun l => if l.isEmpty then s!"{indent} *\n" else s!"{indent} * {l}\n") ++
      s!"{indent} */\n"

def lowerFirst (s : String) : String := (s.take 1).toString.toLower ++ (s.drop 1).toString

/-- A property of a TS object type: a field, or a field whose type is one string literal. -/
inductive Property where
  | field (field : WireField)
  | literal (name value : String)

/-- A TS object type of `properties`, each after its docstring, intersected with the type of each flattened field. -/
def object (indent : String) (properties : List (Option String × Property)) : Write String := do
  let mut lines : List String := []
  let mut flattened : List String := []
  for (doc, p) in properties do
    let doc := (doc.map (jsdoc indent)).getD ""
    match p with
    | .literal n v => lines := lines ++ [doc ++ s!"{indent}readonly {n}: \"{v}\";\n"]
    | .field (.required n t) => lines := lines ++ [doc ++ s!"{indent}readonly {n}: {← tsType t};\n"]
    | .field (.optional n t) => lines := lines ++ [doc ++ s!"{indent}readonly {n}?: {← tsType t};\n"]
    | .field (.flattened _ written) => flattened := flattened ++ [← named written]
  if lines.isEmpty && !flattened.isEmpty then return " & ".intercalate flattened
  let body := if lines.isEmpty then "Readonly<Record<string, never>>"
    else "{\n" ++ String.join lines ++ (indent.drop 2).toString ++ "}"
  return " & ".intercalate (body :: flattened)

def typeDoc (type : Name) : MetaM String := do
  return ((← findDocString? (← getEnv) type).map (jsdoc "")).getD ""

/-- A union of `members`, each after its docstring, an intersection in parentheses. -/
def union (name : String) (doc : String) (members : List (Option String × String)) : String :=
  let member (m : String) := if (m.splitOn "} & ").length > 1 then s!"({m})" else m
  doc ++ s!"export type {name} =\n" ++
    "\n".intercalate (members.map fun (d, m) => ((d.map (jsdoc "  ")).getD "") ++ "  | " ++ member m) ++ ";\n"

/-- The TS declaration of a type with derive_wire, in the shape that `wireShape` decides. -/
def declaration (type : Name) : Write String := do
  let name := type.getString!
  let doc ← typeDoc type
  let fieldDocs (fields : List WireField) : Write (List (Option String × Property)) :=
    fields.mapM fun f => do pure (← findDocString? (← getEnv) (type ++ .mkSimple f.name), .field f)
  let variants (tag : Tag) (ctors : List WireConstructor) : Write (List (Option String × String)) :=
    ctors.mapM fun c => do
      let (before, after) := tag.split c.fields
      let properties := (before.map fun f => (none, Property.field f)) ++ [(none, .literal tag.name c.name)] ++
        after.map fun f => (none, .field f)
      pure (← findDocString? (← getEnv) c.ctor, ← object "      " properties)
  match ← wireShape type with
  | .enum ctors => return doc ++ s!"export type {name} = {" | ".intercalate (ctors.map fun c => s!"\"{c.name}\"")};\n"
  | .object _ fields => return doc ++ s!"export type {name} = {← object "  " (← fieldDocs fields)};\n"
  | .tagged tag ctors => return union name doc (← variants tag ctors)
  | .untagged ctors =>
    return union name doc (← ctors.mapM fun c => do
      pure (← findDocString? (← getEnv) c.ctor, ← object "      " (c.fields.map fun f => (none, .field f))))
  | .flattened _ before body _ _ after =>
    return doc ++ s!"export type {name} = {← object "  " (← fieldDocs (before ++ after ++ [body]))};\n"

/-- The wire fields of constructor `ctor`, which a group's data writes always, as `T | null` for an `Option`. -/
def dataFields (ctor : Name) (fields : List WireField) : MetaM (List (Option String × Property)) :=
  fields.mapM fun
    | field@(.required ..) => pure (none, .field field)
    | field => throwError "{ctor}.{field.name}: a group's data has no optional or flattened field"

def group (type : Name) : Write String := do
  let kinds ← Tazuna.Data.members type
  let members ← kinds.mapM fun member => do
    let fields ← groupFields member
    let definition ← match fields.definition with
      | some type =>
        let ref := match type with
          | .app (.const ``Option _) a => a
          | t => t
        unless ref.isConstOf ``Tazuna.Spec.Ref do
          throwError "{member.ctor}: the argument definition must have type Spec.Ref or Option Spec.Ref"
        tsType type
      | none => pure "null"
    let place ← fields.place.mapM fun (n, type) => do pure s!"      readonly {n}: {← tsType type};\n"
    let data ← dataFields member.ctor (fields.data.map fun (n, t) => .required n t)
    pure (← findDocString? (← getEnv) member.named, "{\n" ++ s!"      readonly kind: \"{kindName type member}\";\n" ++
      s!"      readonly definition: {definition};\n" ++ String.join place ++
      s!"      readonly data: {← object "        " data};\n" ++ "    }")
  let name := type.getString!
  return union name (← typeDoc type) members ++ "\n" ++ constArray s!"{lowerFirst name}Kinds" (kinds.map (kindName type ·))

def modulePaths (types : List Name) : MetaM String := do
  let env ← getEnv
  let modules ← types.mapM fun type => do
    let some module := (env.getModuleIdxFor? type).bind (env.header.moduleNames[·]?)
      | throwError "{type} is not in an imported module"
    pure s!"lean/{"/".intercalate (module.components.map (·.toString))}.lean"
  return ", ".intercalate modules.eraseDups

/-- The `import type` lines of the module `file`, one per imported module, for the TS types that `imports` names. -/
def importLines (file : String) (imports : List (String × String)) : List String :=
  let sources := (imports.map (·.2)).eraseDups.mergeSort fun a b => decide (relativePath file a ≤ relativePath file b)
  sources.map fun source =>
    let types := ((imports.filter (·.2 == source)).map (·.1)).mergeSort fun a b => decide (a ≤ b)
    s!"import type \{ {", ".intercalate types} } from \"{relativePath file source}\";\n"

def header (types : List Name) : MetaM String := do
  return s!"// Generated by npm run lean:write (lean/Generate/Main.lean) from {← modulePaths types}. Do not edit.\n"

/-- The module `path`, whose declarations `parts` writes, with its header and imports. -/
def typesModule (path : String) (parts : Write (List String)) : MetaM (String × String) := do
  let types ← declaredIn path
  let (parts, w) ← parts.run { file := path, declared := types }
  let imports := importLines path w.imports
  return (path, (← header types) ++ String.join imports ++ (if imports.isEmpty then "" else "\n") ++
    "\n".intercalate parts)

/--
`typescript% path` elaborates at build time to the module `path` and its TS source: the group that `modules` lists last
for it, after the types that its data uses.
-/
elab "typescript% " p:str : term => do
  let types ← declaredIn p.getString
  return toExpr (← typesModule p.getString do
    pure ((← types.dropLast.mapM declaration) ++ [← group types.getLast!]))

/-- `types% path` elaborates at build time to the module `path` and the TS types of the wire types it declares. -/
elab "types% " p:str : term => do
  let types ← declaredIn p.getString
  return toExpr (← typesModule p.getString (types.mapM declaration))

def schemaName (type : Name) : String := lowerFirst type.getString!

def enumSchema (ctors : List WireConstructor) : String :=
  "z.enum([" ++ ", ".intercalate (ctors.map fun c => s!"\"{c.name}\"") ++ "])"

/-- The state of writing Zod schemas. `inlined` holds the enum types that the schemas write inline. -/
structure Emitted where
  inlined : List Name := []
  /-- The types that the file declares, so that a schema may name one declared after it. -/
  declared : List Name := []
  /-- Whether the schema being written names a type declared after it, which a getter defers. -/
  forward : Bool := false

abbrev Emit := StateT Emitted MetaM

partial def zodSchema (listed : List Name) : Expr → Emit String
  | .app (.const ``Option _) a => return s!"{← zodSchema listed a}.nullable()"
  | .app (.const ``List _) (.app (.app (.const ``Prod _) (.const ``String _)) a) =>
    return s!"z.record(z.string(), {← zodSchema listed a})"
  | .app (.const ``List _) a => return s!"z.array({← zodSchema listed a})"
  | .const ``String _ => return "z.string()"
  | .const ``Bool _ => return "z.boolean()"
  | .const ``Nat _ => return "z.int().nonnegative()"
  | .const ``Tazuna.Data.Value _ => return "z.unknown()"
  | .const ``Tazuna.Data.DateTime _ => return "z.iso.datetime({ offset: true })"
  | .const ``Tazuna.Data.Time _ => return "z.string()"
  | .app (.app (.const ``Prod _) a) b => return s!"z.tuple([{← zodSchema listed a}, {← zodSchema listed b}])"
  | .app (.const ``Tazuna.Data.FileLine _) a =>
    return s!"z.union([z.null(), z.literal(\"malformed\"), {← zodSchema listed a}])"
  | .const name _ => do
    if listed.contains name then return schemaName name
    if (← get).declared.contains name then
      modify fun e => { e with forward := true }
      return schemaName name
    if let .enum ctors ← wireShape name then
      modify fun e => { e with inlined := if name ∈ e.inlined then e.inlined else e.inlined ++ [name] }
      return enumSchema ctors
    throwError "list {name} before the wire types that use it"
  | type => throwError "no Zod schema for {type}"

/-- A property of an object schema: `name: schema`, or a getter that returns the schema when it names a later type. -/
structure ZodProperty where
  text : String
  doc : Option String := none
  getter : Option (String × String) := none

/-- The property `name` of schema `schema`, a getter when the schema names a type declared after it. -/
def namedProperty (doc : Option String) (name : String) (schema : Emit String) : Emit ZodProperty := do
  modify fun e => { e with forward := false }
  let schema ← schema
  if (← get).forward then return { text := "", doc, getter := some (name, schema) }
  return { text := s!"{name}: {schema}", doc }

def property (listed : List Name) (doc : Option String) : WireField → Emit ZodProperty
  | .required name type => namedProperty doc name (zodSchema listed type)
  | .optional name type => namedProperty doc name do pure s!"{← zodSchema listed type}.exactOptional()"
  | .flattened _ written => do
    unless listed.contains written do throwError "list {written} before the wire types that flatten it"
    pure { text := s!"...{schemaName written}.shape", doc }

def objectSchema (indent : String) (properties : List ZodProperty) : String :=
  "z.object({\n" ++
    String.join (properties.map fun p =>
      ((p.doc.map (jsdoc s!"{indent}  ")).getD "") ++ match p.getter with
        | some (name, schema) =>
          s!"{indent}  get {name}() \{\n{indent}    return {schema};\n{indent}  },\n"
        | none => s!"{indent}  {p.text},\n") ++
    s!"{indent}})"

/-- A `z.discriminatedUnion` of `members`: each variant's schema, after its constructor's docstring. -/
def discriminatedUnion (tag : String) (members : List (Option String × String)) : String :=
  s!"z.discriminatedUnion(\"{tag}\", [\n" ++
    String.join (members.map fun (doc, m) => ((doc.map (jsdoc "  ")).getD "") ++ s!"  {m},\n") ++ "])"

/-- A `z.union` of `members`: each constructor's schema, after its docstring. -/
def unionSchema (members : List (Option String × String)) : String :=
  "z.union([\n" ++
    String.join (members.map fun (doc, m) => ((doc.map (jsdoc "  ")).getD "") ++ s!"  {m},\n") ++ "])"

def variants (listed : List Name) (tag : Tag) (ctors : List WireConstructor) (before after : List ZodProperty) :
    Emit (List (Option String × String)) :=
  ctors.mapM fun c => do
    let (beforeTag, afterTag) := tag.split c.fields
    let tagProperty : ZodProperty := { text := s!"{tag.name}: z.literal(\"{c.name}\")" }
    let fields := (← beforeTag.mapM (property listed none)) ++ [tagProperty] ++ (← afterTag.mapM (property listed none))
    pure (← findDocString? (← getEnv) c.ctor, objectSchema "  " (before ++ fields ++ after))

def schemaOf (listed : List Name) (type : Name) : Emit String := do
  let fieldProperty (field : WireField) : Emit ZodProperty := do
    property listed (← findDocString? (← getEnv) (type ++ .mkSimple field.name)) field
  match ← wireShape type with
  | .enum ctors => return enumSchema ctors
  | .tagged tag ctors => return discriminatedUnion tag.name (← variants listed tag ctors [] [])
  | .object _ fields => return objectSchema "" (← fields.mapM fieldProperty)
  | .untagged ctors =>
    return unionSchema (← ctors.mapM fun c => do
      pure (← findDocString? (← getEnv) c.ctor, objectSchema "  " (← c.fields.mapM (property listed none))))
  | .flattened _ before _ tag ctors after =>
    let before ← before.mapM fieldProperty
    return discriminatedUnion tag.name (← variants listed tag ctors before (← after.mapM fieldProperty))

/-- A type that TS parses: its schema, exported for the root, and its type. -/
def zodDeclaration (listed : List Name) (exported : Bool) (type : Name) : Emit String := do
  return s!"{if exported then "export " else ""}const {schemaName type} = {← schemaOf listed type};\n\n" ++
    (← typeDoc type) ++ s!"export type {type.getString!} = z.infer<typeof {schemaName type}>;\n"

/-- `zod% path` elaborates to the module `path` and the Zod schemas of the wire types that it declares, which TS parses. -/
elab "zod% " p:str : term => do
  let types ← declaredIn p.getString
  let declarations : Emit (List String) := do
    let mut listed : List Name := []
    let mut declarations : List String := []
    for type in types do
      declarations := declarations ++ [← zodDeclaration listed (type == types.getLast!) type]
      listed := listed ++ [type]
    return declarations
  let (declarations, emitted) ← declarations.run { declared := types }
  return toExpr (p.getString, (← header (types ++ emitted.inlined)) ++ "import { z } from \"zod\";\n\n" ++
    "\n".intercalate declarations)

/-- `groupSamples% T` elaborates to one value per kind of group `T`, with `default` arguments, in declaration order. -/
elab "groupSamples% " t:ident : term => do
  let group ← realizeGlobalConstNoOverloadWithInfo t
  let sample (ctor : Name) (flattened : Option (String × Expr)) : MetaM Expr := do
    forallTelescope (← getConstInfoCtor ctor).type fun args _ => do
      let values ← args.mapM fun a => do
        if let some (field, value) := flattened then
          if (← a.fvarId!.getUserName).toString == field then return value
        mkAppOptM ``Inhabited.default #[← inferType a, none]
      pure (mkAppN (mkConst ctor) values)
  let values ← (← members group).mapM fun m => do
    match m.inner with
    | none => sample m.ctor none
    | some (field, inner) => sample m.ctor (some (field, ← sample inner none))
  mkListLit (mkConst group) values

/--
The TS constant `halting<type>Kinds`: the kinds, in declaration order, whose violations halt the run. `halts` depends
only on the kind, so one sample per kind decides it.
-/
def halting (type : String) (kinds : List String) : String :=
  "\n/** The kinds whose violations halt the run. */\n" ++ constArray s!"halting{type}Kinds" kinds

/-- `doc% c` elaborates to the docstring of `c`. -/
elab "doc% " c:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo c
  let some doc ← findDocString? (← getEnv) name | throwError "{name} has no docstring"
  return toExpr doc

/-- `constructorDocs% T` elaborates to the docstrings of the constructors of `T`, in declaration order. -/
elab "constructorDocs% " t:ident : term => do
  let type ← realizeGlobalConstNoOverloadWithInfo t
  let docs ← (← constructors type).mapM fun c => do
    let some doc ← findDocString? (← getEnv) c | throwError "{c} has no docstring"
    pure doc
  return toExpr docs

/-- `sources% c+` elaborates to the Lean files that declare `c`, as a generated file's header names them. -/
elab "sources% " cs:ident+ : term => do
  return toExpr (← modulePaths (← cs.toList.mapM fun c => realizeGlobalConstNoOverloadWithInfo c.raw))

/-- The TS limits: `limits`, Limit.max by limit name, and the limits of the searches and of a comparison. -/
def limitsFile : String :=
  let constant (name doc : String) (value : Nat) := "\n" ++ jsdoc "" doc ++ s!"export const {name} = {value};\n"
  "// Generated by npm run lean:write (lean/Generate/Main.lean) from " ++
    sources% Tazuna.Service.Limit Tazuna.Explore.stepOrderLimit Tazuna.Data.bindingLimit ++ ". Do not edit.\n" ++
    jsdoc "" (doc% Tazuna.Service.Limit) ++ "export const limits = {\n" ++
    String.join (((samples% Tazuna.Service.Limit).zip (constructorDocs% Tazuna.Service.Limit)).map fun (l, doc) =>
      jsdoc "  " doc ++ s!"  {l.name}: {l.max},\n") ++ "} as const;\n" ++
    constant "stepOrderLimit" (doc% Tazuna.Explore.stepOrderLimit) Tazuna.Explore.stepOrderLimit ++
    constant "bindingLimit" (doc% Tazuna.Data.bindingLimit) Tazuna.Data.bindingLimit

/-- The TS constant `byCallerKinds`: the rejection kinds, in declaration order, that blame the request. -/
def byCallerKinds : String :=
  "\n/** The rejection kinds that blame the request, not the target's availability. */\n" ++
    constArray "byCallerKinds" ((samples% Tazuna.Data.RejectionKind).filterMap fun k =>
      match ToValue.toValue k with
      | .str s => if k.byCaller then some s else none
      | _ => none)

/-- The module `file` with `extra` appended. -/
def appended (file : String × String) (extra : String) : String × String := (file.1, file.2 ++ extra)

def files : List (String × String) :=
  [typescript% "src/data/illegal.generated.ts",
   typescript% "src/data/mismatch.generated.ts",
   typescript% "src/data/uncomparable.generated.ts",
   appended (typescript% "src/data/invalidInput.generated.ts")
     (halting "InvalidInput" (((groupSamples% Tazuna.Service.InvalidInput).filter (·.halts)).map (·.kind))),
   appended (typescript% "src/data/invalidScenario.generated.ts")
     (halting "InvalidScenario" (((groupSamples% Tazuna.Sim.InvalidScenario).filter (·.halts)).map (·.kind))),
   zod% "src/data/scenario.generated.ts",
   appended (typescript% "src/data/fault.generated.ts")
     (halting "Fault" (((groupSamples% Tazuna.Service.Fault).filter (·.halts)).map (·.kind))),
   typescript% "src/data/bagOrderDependent.generated.ts",
   typescript% "src/data/choiceDependent.generated.ts",
   types% "src/data/transitionRef.generated.ts",
   types% "src/data/step.generated.ts",
   appended (zod% "src/data/trace.generated.ts") byCallerKinds,
   ("src/data/limits.generated.ts", limitsFile),
   types% "src/spec/structure.generated.ts",
   types% "test/lean/protocol.generated.ts"]

/--
The entry point. Without `--write`, it exits 1 when a file differs from the Lean definitions or is missing, and writes
nothing. With `--write`, it writes the files that differ.
-/
def main (args : List String) : IO UInt32 := do
  let some (write, folder) := match args with
      | [folder] => some (false, folder)
      | ["--write", folder] => some (true, folder)
      | _ => none
    | IO.eprintln "usage: tazuna-generate [--write] <repository folder>"; return 2
  let mut stale := false
  for (file, text) in files do
    let path := System.FilePath.mk folder / file
    let present ← path.pathExists
    if present then
      if (← IO.FS.readFile path) == text then continue
    if write then
      IO.FS.writeFile path text
    else
      IO.eprintln s!"tazuna-generate: {path} {if present then "differs from the Lean definitions" else "is missing"}."
      stale := true
  if stale then
    IO.eprintln "tazuna-generate: run npm run lean:write -w tazuna to regenerate."
    return 1
  return 0
