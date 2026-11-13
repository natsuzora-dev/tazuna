import Lean.Elab.Term
import Tazuna.Data.Names
import Tazuna.Semantics.Step
import Tazuna.Data.Trace
import Tazuna.Observe.ChoiceDependent
import Tazuna.Observe.OrderDependent
import Tazuna.Semantics.Fault
import Tazuna.Semantics.InvalidInput
import Tazuna.Syntax.Structure
import Tazuna.Validation.Illegal
import Tazuna.Verify.Mismatch
import Tazuna.Verify.Uncomparable

/-!
The text is laid out as Biome formats it, since `npm run lint` checks it.

A violation type and a wire type (Data/Wire.lean) differ in two ways. A violation's `Option` field is always `T | null`,
and a wire type's is an optional property (`.exactOptional()`) under skip_serializing_none. A violation's constructor is
named by its `kind` (`"Group.constructor"`), and a wire type's constructor by its `tag` field, whose value is the
constructor's name, kebab-case under rename_all.
-/

open Lean Elab Term Meta Tazuna.Data

structure TsType where
  lean : Name
  ts : String
  module : Option String

def tsTypes : List TsType :=
  [⟨``String, "string", none⟩, ⟨``Nat, "number", none⟩, ⟨``Tazuna.Data.Value, "Json", some "./values.ts"⟩,
   ⟨``Tazuna.Syntax.Ref, "DefinitionRef", some "./definitionRef.ts"⟩,
   ⟨``Tazuna.Verify.Subject, "Subject", some "./mismatch.generated.ts"⟩,
   ⟨``Tazuna.Verify.Use, "Use", none⟩,
   ⟨``Tazuna.Data.RejectionKind, "RejectionKind", some "./trace.generated.ts"⟩,
   ⟨``Tazuna.Data.Rejection, "Rejection", some "./trace.generated.ts"⟩,
   ⟨``Tazuna.Data.DeadlineId, "DeadlineId", some "./trace.generated.ts"⟩, ⟨``Tazuna.Data.Time, "string", none⟩,
   ⟨``Tazuna.Syntax.TransitionRef, "TransitionRef", some "./transitionRef.ts"⟩,
   ⟨``Tazuna.Semantics.Copy, "Copy", some "./choiceDependent.generated.ts"⟩,
   ⟨``Tazuna.Semantics.Who, "Who", some "./choiceDependent.generated.ts"⟩,
   ⟨``Tazuna.Semantics.StepName, "StepName", some "./choiceDependent.generated.ts"⟩,
   ⟨``Tazuna.Semantics.Violation, "ViolationValue", some "./violation.ts"⟩,
   ⟨``Tazuna.Observe.Difference, "Difference", none⟩]

/-- The TS type of a Lean type. The state collects the imports that the TS type needs. -/
partial def tsType : Expr → StateT (List (String × String)) MetaM String
  | .app (.const ``Option _) a => return s!"{← tsType a} | null"
  | .app (.const ``List _) a => return s!"readonly {← tsType a}[]"
  | .const name _ => do
    let some t := tsTypes.find? (·.lean == name) | throwError "tsTypes has no TS type for {name}"
    if let some path := t.module then
      modify fun imports => if (t.ts, path) ∈ imports then imports else imports ++ [(t.ts, path)]
    return t.ts
  | type => throwError "tsTypes has no TS type for {type}"

def jsdoc (indent doc : String) : String :=
  match (doc.trimAscii.toString.splitOn "\n").map (·.trimAsciiStart.toString) with
  | [line] => s!"{indent}/** {line} */\n"
  | lines =>
    s!"{indent}/**\n" ++
      String.join (lines.map fun l => if l.isEmpty then s!"{indent} *\n" else s!"{indent} * {l}\n") ++
      s!"{indent} */\n"

def lowerFirst (s : String) : String := (s.take 1).toString.toLower ++ (s.drop 1).toString

/-- A TS object type. `literals` are the fields whose type is one string literal, and they come first. -/
def object (fields : List (String × Expr)) (indent : String) (literals : List (String × String) := []) :
    StateT (List (String × String)) MetaM String := do
  let lines := literals.map (fun (n, v) => s!"{indent}readonly {n}: \"{v}\";\n") ++
    (← fields.mapM fun (n, type) => do pure s!"{indent}readonly {n}: {← tsType type};\n")
  if lines.isEmpty then return "Readonly<Record<string, never>>"
  return "{\n" ++ String.join lines ++ (indent.drop 2).toString ++ "}"

def union (name : Name) (doc : String) (members : List String) : String :=
  doc ++ s!"export type {name.getString!} =\n" ++ "\n".intercalate (members.map ("  | " ++ ·)) ++ ";\n"

/-- The wire fields of constructor `ctor`, which a group's data writes always, as `T | null` for an `Option`. -/
def dataFields (ctor : Name) (fields : List WireField) : MetaM (List (String × Expr)) :=
  fields.mapM fun
    | .required name type => pure (name, type)
    | field => throwError "{ctor}.{field.name}: a group's data has no optional or flattened field"

/-- The TS type of a type with derive_wire that a group's data uses, in the shape that `wireShape` decides. -/
def value (type : Name) : StateT (List (String × String)) MetaM String := do
  let doc := (← findDocString? (← getEnv) type).map (jsdoc "") |>.getD ""
  match ← wireShape type with
  | .untagged ctors => return union type doc (← ctors.mapM fun c => do object (← dataFields c.ctor c.fields) "      ")
  | .tagged tag ctors =>
    return union type doc
      (← ctors.mapM fun c => do object (← dataFields c.ctor c.fields) "      " [(tag.name, c.name)])
  | .object ctor fields =>
    return doc ++ s!"export type {type.getString!} = {← object (← dataFields ctor fields) "  "};\n"
  | _ => throwError "{type}: a group's data has only untagged, tagged and object types"

def group (type : Name) : StateT (List (String × String)) MetaM String := do
  let ctors ← constructors type
  let members ← ctors.mapM fun ctor => do
    let fields ← groupFields ctor
    let definition ← match fields.definition with
      | some type =>
        let ref := match type with
          | .app (.const ``Option _) a => a
          | t => t
        unless ref.isConstOf ``Tazuna.Syntax.Ref do
          throwError "{ctor}: the argument definition must have type Syntax.Ref or Option Syntax.Ref"
        tsType type
      | none => pure "null"
    let place ← fields.place.mapM fun (n, type) => do pure s!"      readonly {n}: {← tsType type};\n"
    let doc := ((← findDocString? (← getEnv) ctor).map (jsdoc "  ")).getD ""
    pure (doc, "{\n" ++ s!"      readonly kind: \"{kindName type ctor}\";\n" ++
      s!"      readonly definition: {definition};\n" ++ String.join place ++
      s!"      readonly data: {← object fields.data "        "};\n" ++ "    }")
  let name := type.getString!
  let kinds := String.join (ctors.map fun ctor => s!"  \"{kindName type ctor}\",\n")
  let typeDoc := (← findDocString? (← getEnv) type).map (jsdoc "") |>.getD ""
  return typeDoc ++ s!"export type {name} =\n" ++
    "\n".intercalate (members.map fun (doc, m) => doc ++ "  | " ++ m) ++ ";\n\n" ++
    s!"export const {lowerFirst name}Kinds = [\n{kinds}] as const;\n"

/-- The `import type` lines, one per module, for the TS types that `imports` names. -/
def importLines (imports : List (String × String)) : List String :=
  let sources := (imports.map (·.2)).eraseDups.mergeSort fun a b => decide (a ≤ b)
  sources.map fun source =>
    let types := ((imports.filter (·.2 == source)).map (·.1)).mergeSort fun a b => decide (a ≤ b)
    s!"import type \{ {", ".intercalate types} } from \"{source}\";\n"

/--
`typescript% T values*` elaborates at build time to the TS source of group `T`, after the types `values` that its data
uses, which the file declares instead of importing.
-/
elab "typescript% " t:ident values:ident* : term => do
  let type ← realizeGlobalConstNoOverloadWithInfo t
  let env ← getEnv
  let some module := (env.getModuleIdxFor? type).bind (env.header.moduleNames[·]?)
    | throwError "{type} is not in an imported module"
  let values ← values.toList.mapM fun v => realizeGlobalConstNoOverloadWithInfo v.raw
  let parts : StateT (List (String × String)) MetaM (List String) := do
    pure ((← values.mapM value) ++ [← group type])
  let (parts, imports) ← parts.run []
  let imports := imports.filter fun (t, _) => !values.any (·.getString! == t)
  let path := "/".intercalate (module.components.map (·.toString))
  return toExpr (s!"// Generated by npm run lean:write (lean/Generate/Main.lean) from lean/{path}.lean. Do not edit.\n" ++
    String.join (importLines imports) ++ "\n" ++ "\n".intercalate parts)

def schemaName (type : Name) : String := lowerFirst type.getString!

def enumSchema (ctors : List WireConstructor) : String :=
  "z.enum([" ++ ", ".intercalate (ctors.map fun c => s!"\"{c.name}\"") ++ "])"

/--
The state of writing Zod schemas. `inlined` holds the enum types that the schemas write inline. `imports` holds the TS
types, with their modules, that `z.custom` names; only a file that TS never parses (`custom`) writes `z.custom`.
-/
structure Emitted where
  inlined : List Name := []
  imports : List (String × String) := []
  custom : Bool

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
  | .const name _ => do
    if listed.contains name then return schemaName name
    if let .enum ctors ← wireShape name then
      modify fun e => { e with inlined := if name ∈ e.inlined then e.inlined else e.inlined ++ [name] }
      return enumSchema ctors
    let some { ts, module := some path, .. } := tsTypes.find? (·.lean == name)
      | throwError "list {name} before the wire types that use it"
    unless (← get).custom do throwError "list {name} before the wire types that use it"
    modify fun e => { e with imports := if (ts, path) ∈ e.imports then e.imports else e.imports ++ [(ts, path)] }
    return s!"z.custom<{ts}>()"
  | type => throwError "no Zod schema for {type}"

structure Property where
  text : String
  doc : Option String := none

def property (listed : List Name) (doc : Option String) : WireField → Emit Property
  | .required name type => do pure { text := s!"{name}: {← zodSchema listed type}", doc }
  | .optional name type => do pure { text := s!"{name}: {← zodSchema listed type}.exactOptional()", doc }
  | .flattened _ written => do
    unless listed.contains written do throwError "list {written} before the wire types that flatten it"
    pure { text := s!"...{schemaName written}.shape", doc }

def objectSchema (indent : String) (properties : List Property) : String :=
  "z.object({\n" ++
    String.join (properties.map fun p =>
      ((p.doc.map (jsdoc s!"{indent}  ")).getD "") ++ s!"{indent}  {p.text},\n") ++
    s!"{indent}})"

/-- A `z.discriminatedUnion` of `members`: each variant's schema, after its constructor's docstring. -/
def discriminatedUnion (tag : String) (members : List (Option String × String)) : String :=
  s!"z.discriminatedUnion(\"{tag}\", [\n" ++
    String.join (members.map fun (doc, m) => ((doc.map (jsdoc "  ")).getD "") ++ s!"  {m},\n") ++ "])"

/-- A `z.union` of `members`: each constructor's schema, after its docstring. -/
def unionSchema (members : List (Option String × String)) : String :=
  "z.union([\n" ++
    String.join (members.map fun (doc, m) => ((doc.map (jsdoc "  ")).getD "") ++ s!"  {m},\n") ++ "])"

def variants (listed : List Name) (tag : Tag) (ctors : List WireConstructor) (before after : List Property) :
    Emit (List (Option String × String)) :=
  ctors.mapM fun c => do
    let (beforeTag, afterTag) := tag.split c.fields
    let tagProperty : Property := { text := s!"{tag.name}: z.literal(\"{c.name}\")" }
    let fields := (← beforeTag.mapM (property listed none)) ++ [tagProperty] ++ (← afterTag.mapM (property listed none))
    pure (← findDocString? (← getEnv) c.ctor, objectSchema "  " (before ++ fields ++ after))

def schemaOf (listed : List Name) (type : Name) : Emit String := do
  let fieldProperty (field : WireField) : Emit Property := do
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

def typeDoc (type : Name) : MetaM String := do
  return ((← findDocString? (← getEnv) type).map (jsdoc "")).getD ""

/-- A type that TS names: its schema, exported when TS parses it, and its type. -/
def declaration (listed : List Name) (exported : Bool) (type : Name) : Emit String := do
  return s!"{if exported then "export " else ""}const {schemaName type} = {← schemaOf listed type};\n\n" ++
    (← typeDoc type) ++ s!"export type {type.getString!} = z.infer<typeof {schemaName type}>;\n"

/-- A type that TS does not name: only its schema. -/
def schemaDeclaration (listed : List Name) (type : Name) : Emit String := do
  return (← typeDoc type) ++ s!"const {schemaName type} = {← schemaOf listed type};\n"

def modulePaths (types : List Name) : MetaM String := do
  let env ← getEnv
  let modules ← types.mapM fun type => do
    let some module := (env.getModuleIdxFor? type).bind (env.header.moduleNames[·]?)
      | throwError "{type} is not in an imported module"
    pure s!"lean/{"/".intercalate (module.components.map (·.toString))}.lean"
  return ", ".intercalate modules.eraseDups

def zodFile (declared : List Name) (custom : Bool) (declarations : Emit (List String)) : MetaM String := do
  let (declarations, emitted) ← declarations.run { custom }
  let header := s!"// Generated by npm run lean:write (lean/Generate/Main.lean) from {← modulePaths (declared ++ emitted.inlined)}."
  return header ++ " Do not edit.\n" ++ "import { z } from \"zod\";\n" ++ String.join (importLines emitted.imports) ++
    "\n" ++ "\n".intercalate declarations

/--
`zod% T parts*` elaborates to the Zod schemas of wire type `T`, which TS parses, after the wire types `parts` that it
uses.
-/
elab "zod% " t:ident parts:ident* : term => do
  let root ← realizeGlobalConstNoOverloadWithInfo t
  let parts ← parts.toList.mapM fun p => realizeGlobalConstNoOverloadWithInfo p.raw
  let declarations : Emit (List String) := do
    let mut listed : List Name := []
    let mut declarations : List String := []
    for type in parts do
      declarations := declarations ++ [← declaration listed false type]
      listed := listed ++ [type]
    return declarations ++ [← declaration listed true root]
  return toExpr (← zodFile (parts ++ [root]) false declarations)

/--
`zodType% T parts*` elaborates to the TS type of wire type `T`, which TS writes but never parses, taken with `z.infer`
from schemas that are not exported, after the wire types `parts` that it uses. A type that another generated file
declares in TS is written as `z.custom` of that TS type.
-/
elab "zodType% " t:ident parts:ident* : term => do
  let root ← realizeGlobalConstNoOverloadWithInfo t
  let parts ← parts.toList.mapM fun p => realizeGlobalConstNoOverloadWithInfo p.raw
  let declarations : Emit (List String) := do
    let mut listed : List Name := []
    let mut declarations : List String := []
    for type in parts do
      declarations := declarations ++ [← schemaDeclaration listed type]
      listed := listed ++ [type]
    return declarations ++ [← declaration listed false root]
  return toExpr (← zodFile (parts ++ [root]) true declarations)

/--
The TS constant `halting<type>Kinds`: the kinds, in declaration order, whose violations halt the run. `halts` depends
only on the constructor, so one sample per constructor decides it.
-/
def halting (type : String) (kinds : List String) : String :=
  s!"\n/** The kinds whose violations halt the run. */\nexport const halting{type}Kinds = [\n" ++
    String.join (kinds.map fun k => s!"  \"{k}\",\n") ++ "] as const;\n"

def files : List (String × String) :=
  [("data/illegal.generated.ts", typescript% Tazuna.Validation.Illegal),
   ("data/mismatch.generated.ts", typescript% Tazuna.Verify.Mismatch Tazuna.Verify.Subject Tazuna.Verify.Use),
   ("data/uncomparable.generated.ts", typescript% Tazuna.Verify.Uncomparable),
   ("data/invalidInput.generated.ts", typescript% Tazuna.Semantics.InvalidInput ++
      halting "InvalidInput" (((samples% Tazuna.Semantics.InvalidInput).filter (·.halts)).map (·.kind))),
   ("data/fault.generated.ts", typescript% Tazuna.Semantics.Fault ++
      halting "Fault" (((samples% Tazuna.Semantics.Fault).filter (·.halts)).map (·.kind))),
   ("data/orderDependent.generated.ts", typescript% Tazuna.Observe.OrderDependent),
   ("data/choiceDependent.generated.ts",
    typescript% Tazuna.Observe.ChoiceDependent Tazuna.Semantics.Copy Tazuna.Semantics.Who Tazuna.Semantics.StepName
      Tazuna.Observe.Difference),
   ("data/trace.generated.ts",
    zod% Tazuna.Data.TraceLine Tazuna.Data.RejectionKind Tazuna.Data.Rejection Tazuna.Data.Answer
      Tazuna.Data.DeadlineId),
   ("syntax/structure.generated.ts",
    zodType% Tazuna.Syntax.Structure Tazuna.Data.RejectionKind Tazuna.Syntax.Ref Tazuna.Syntax.Activity
      Tazuna.Syntax.Transition Tazuna.Syntax.State Tazuna.Syntax.ChartFields Tazuna.Syntax.Reference
      Tazuna.Syntax.Definition Tazuna.Syntax.Contract Tazuna.Syntax.ServiceInfo Tazuna.Syntax.ScenarioInput Tazuna.Syntax.Scenario),
   ("data/step.generated.ts",
    zodType% Tazuna.Semantics.Step Tazuna.Data.Rejection Tazuna.Data.Answer Tazuna.Data.DeadlineId
      Tazuna.Semantics.Choice)]

/--
The entry point. Without `--write`, it exits 1 when a file differs from the Lean definitions or is missing, and writes
nothing. With `--write`, it writes the files that differ.
-/
def main (args : List String) : IO UInt32 := do
  let some (write, folder) := match args with
      | [folder] => some (false, folder)
      | ["--write", folder] => some (true, folder)
      | _ => none
    | IO.eprintln "usage: tazuna-generate [--write] <TS source folder>"; return 2
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
