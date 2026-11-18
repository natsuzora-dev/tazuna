import Lean.Elab.Term
import Tazuna.Data.Names
import Tazuna.Service.Limits
import Tazuna.Data.Trace
import Tazuna.Explore.ChoiceDependent
import Tazuna.Explore.BagOrderDependent
import Tazuna.Service.Fault
import Tazuna.Service.InvalidInput
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
and a wire type's is an optional property (`.exactOptional()`) under skip_serializing_none. A violation's constructor is
named by its `kind` (`"Group.constructor"`), and a wire type's constructor by its `tag` field, whose value is the
constructor's name, kebab-case under rename_all.
-/

open Lean Elab Term Meta Tazuna.Data

structure TsType where
  lean : Name
  ts : String
  module : Option String

/--
The TS constant `name`: the strings `values` as a const array, on one line when it fits in 120 columns and one string
per line otherwise, as Biome formats it.
-/
def constArray (name : String) (values : List String) : String :=
  let quoted := values.map fun v => s!"\"{v}\""
  let oneLine := s!"export const {name} = [{", ".intercalate quoted}] as const;"
  if oneLine.length ≤ 120 then oneLine ++ "\n"
  else s!"export const {name} = [\n" ++ String.join (quoted.map fun q => s!"  {q},\n") ++ "] as const;\n"

def tsTypes : List TsType :=
  [⟨``String, "string", none⟩, ⟨``Nat, "number", none⟩, ⟨``Bool, "boolean", none⟩, ⟨``Tazuna.Data.Value, "Json", some "./values.ts"⟩,
   ⟨``Tazuna.Spec.Ref, "DefinitionRef", some "./definitionRef.ts"⟩,
   ⟨``Tazuna.Verify.Subject, "Subject", some "./mismatch.generated.ts"⟩,
   ⟨``Tazuna.Data.RejectionKind, "RejectionKind", some "./trace.generated.ts"⟩,
   ⟨``Tazuna.Data.Rejection, "Rejection", some "./trace.generated.ts"⟩,
   ⟨``Tazuna.Data.Time, "string", none⟩,
   ⟨``Tazuna.Spec.CallOutcome, "CallOutcome", some "../data/transitionRef.generated.ts"⟩,
   ⟨``Tazuna.Spec.SendOutcome, "SendOutcome", some "../data/transitionRef.generated.ts"⟩,
   ⟨``Tazuna.Spec.TransitionRef, "TransitionRef", some "../data/transitionRef.generated.ts"⟩,
   ⟨``Tazuna.Spec.Trigger, "Trigger", some "../data/transitionRef.generated.ts"⟩,
   ⟨``Tazuna.Service.InstanceId, "InstanceId", some "./step.generated.ts"⟩,
   ⟨``Tazuna.Service.Requester, "Requester", some "./step.generated.ts"⟩,
   ⟨``Tazuna.Service.Received, "Received", some "./step.generated.ts"⟩,
   ⟨``Tazuna.Service.StepName, "StepName", some "./step.generated.ts"⟩,
   ⟨``Tazuna.Data.Violation, "ViolationValue", some "./violation.ts"⟩,
   ⟨``Tazuna.Explore.Difference, "Difference", none⟩, ⟨``Tazuna.Explore.Assigned, "Assigned", none⟩,
   ⟨``Tazuna.Data.TraceLine, "TraceLine", some "./trace.generated.ts"⟩,
   ⟨``Tazuna.Data.Answer, "Answer", some "./trace.generated.ts"⟩,
   ⟨``Tazuna.Scenario, "Scenario", some "./scenario.generated.ts"⟩,
   ⟨``Tazuna.Scenario.Origin, "Origin", some "./scenario.generated.ts"⟩,
   ⟨``Tazuna.Spec.Structure, "Structure", some "../spec/structure.generated.ts"⟩,
   ⟨``Tazuna.Service.Activity, "Activity", some "./step.generated.ts"⟩,
   ⟨``Tazuna.Verify.Scenario, "PairingScenario", some "../verify/pairing.ts"⟩,
   ⟨``Tazuna.Verify.Folder, "Folder", some "../verify/pairing.ts"⟩]

/-- The TS type of a Lean type. The state collects the imports that the TS type needs. -/
partial def tsType : Expr → StateT (List (String × String)) MetaM String
  | .app (.const ``Option _) a => return s!"{← tsType a} | null"
  | .app (.const ``List _) a => do
    let t ← tsType a
    return if t.startsWith "readonly " || (t.splitOn " | ").length > 1 then s!"readonly ({t})[]" else s!"readonly {t}[]"
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
  | .enum ctors => return doc ++ s!"export type {type.getString!} = {" | ".intercalate (ctors.map fun c => s!"\"{c.name}\"")};\n"
  | _ => throwError "{type}: a group's data has only enum, untagged, tagged and object types"

def group (type : Name) : StateT (List (String × String)) MetaM String := do
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
    let doc := ((← findDocString? (← getEnv) member.named).map (jsdoc "  ")).getD ""
    pure (doc, "{\n" ++ s!"      readonly kind: \"{kindName type member}\";\n" ++
      s!"      readonly definition: {definition};\n" ++ String.join place ++
      s!"      readonly data: {← object fields.data "        "};\n" ++ "    }")
  let name := type.getString!
  let typeDoc := (← findDocString? (← getEnv) type).map (jsdoc "") |>.getD ""
  return typeDoc ++ s!"export type {name} =\n" ++
    "\n".intercalate (members.map fun (doc, m) => doc ++ "  | " ++ m) ++ ";\n\n" ++
    constArray s!"{lowerFirst name}Kinds" (kinds.map (kindName type ·))

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

/-- `types% T+` elaborates at build time to the TS types of the wire types `T`, which a group's data uses. -/
elab "types% " ts:ident+ : term => do
  let types ← ts.toList.mapM fun t => realizeGlobalConstNoOverloadWithInfo t.raw
  let (parts, imports) ← (types.mapM value).run []
  let imports := imports.filter fun (t, _) => !types.any (·.getString! == t)
  let env ← getEnv
  let modules := types.filterMap fun type => (env.getModuleIdxFor? type).bind (env.header.moduleNames[·]?)
  let paths := modules.eraseDups.map fun m => s!"lean/{"/".intercalate (m.components.map (·.toString))}.lean"
  return toExpr (s!"// Generated by npm run lean:write (lean/Generate/Main.lean) from {", ".intercalate paths}. Do not edit.\n" ++
    String.join (importLines imports) ++ (if imports.isEmpty then "" else "\n") ++ "\n".intercalate parts)

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
    let some { ts, module := some path, .. } := tsTypes.find? (·.lean == name)
      | throwError "list {name} before the wire types that use it"
    unless (← get).custom do throwError "list {name} before the wire types that use it"
    modify fun e => { e with imports := if (ts, path) ∈ e.imports then e.imports else e.imports ++ [(ts, path)] }
    return s!"z.custom<{ts}>()"
  | type => throwError "no Zod schema for {type}"

/-- A property of an object schema: `name: schema`, or a getter that returns the schema when it names a later type. -/
structure Property where
  text : String
  doc : Option String := none
  getter : Option (String × String) := none

/-- The property `name` of schema `schema`, a getter when the schema names a type declared after it. -/
def namedProperty (doc : Option String) (name : String) (schema : Emit String) : Emit Property := do
  modify fun e => { e with forward := false }
  let schema ← schema
  if (← get).forward then return { text := "", doc, getter := some (name, schema) }
  return { text := s!"{name}: {schema}", doc }

def property (listed : List Name) (doc : Option String) : WireField → Emit Property
  | .required name type => namedProperty doc name (zodSchema listed type)
  | .optional name type => namedProperty doc name do pure s!"{← zodSchema listed type}.exactOptional()"
  | .flattened _ written => do
    unless listed.contains written do throwError "list {written} before the wire types that flatten it"
    pure { text := s!"...{schemaName written}.shape", doc }

def objectSchema (indent : String) (properties : List Property) : String :=
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

/--
The module `path`, which `tsTypes` names from a folder of src, as a file in another folder names it: `src` is that
file's path to src.
-/
def relocated (src : Option String) (path : String) : String :=
  match src with
  | none => path
  | some src =>
    if path.startsWith "./" then src ++ "data/" ++ (path.drop 2).toString
    else if path.startsWith "../" then src ++ (path.drop 3).toString
    else path

def zodFile (declared : List Name) (custom : Bool) (declarations : Emit (List String)) (src : Option String := none) :
    MetaM String := do
  let (declarations, emitted) ← declarations.run { custom }
  let header := s!"// Generated by npm run lean:write (lean/Generate/Main.lean) from {← modulePaths (declared ++ emitted.inlined)}."
  let imports := emitted.imports.map fun (t, path) => (t, relocated src path)
  return header ++ " Do not edit.\n" ++ "import { z } from \"zod\";\n" ++ String.join (importLines imports) ++
    "\n" ++ "\n".intercalate declarations

/--
`zod% T parts*` elaborates to the Zod schemas of wire type `T`, which TS parses, after the wire types `parts` that it
uses.
-/
elab "zod% " t:ident parts:ident* : term => do
  let root ← realizeGlobalConstNoOverloadWithInfo t
  let parts ← parts.toList.mapM fun p => realizeGlobalConstNoOverloadWithInfo p.raw
  let declarations : Emit (List String) := do
    modify fun e => { e with declared := parts ++ [root] }
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
`zodTypes% src T+` elaborates to the TS types of the wire types `T`, which TS writes but never parses, each taken with
`z.infer` from a schema that is not exported, for a file outside src whose path to src is `src`.
-/
elab "zodTypes% " src:str ts:ident+ : term => do
  let types ← ts.toList.mapM fun t => realizeGlobalConstNoOverloadWithInfo t.raw
  let declarations : Emit (List String) := do
    let mut listed : List Name := []
    let mut declarations : List String := []
    for type in types do
      declarations := declarations ++ [← declaration listed false type]
      listed := listed ++ [type]
    return declarations
  return toExpr (← zodFile types true declarations (some src.getString))

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
    constant "assignmentLimit" (doc% Tazuna.Explore.assignmentLimit) Tazuna.Explore.assignmentLimit ++
    constant "bindingLimit" (doc% Tazuna.Data.bindingLimit) Tazuna.Data.bindingLimit

/-- The TS constant `byCallerKinds`: the rejection kinds, in declaration order, that blame the request. -/
def byCallerKinds : String :=
  "\n/** The rejection kinds that blame the request, not the target's availability. */\n" ++
    constArray "byCallerKinds" ((samples% Tazuna.Data.RejectionKind).filterMap fun k =>
      match ToValue.toValue k with
      | .str s => if k.byCaller then some s else none
      | _ => none)

def files : List (String × String) :=
  [("src/data/illegal.generated.ts", typescript% Tazuna.Validation.Illegal),
   ("src/data/mismatch.generated.ts", typescript% Tazuna.Verify.Mismatch Tazuna.Verify.Subject),
   ("src/data/uncomparable.generated.ts", typescript% Tazuna.Verify.Uncomparable),
   ("src/data/invalidInput.generated.ts", typescript% Tazuna.Service.InvalidInput ++
      halting "InvalidInput" (((groupSamples% Tazuna.Service.InvalidInput).filter (·.halts)).map (·.kind))),
   ("src/data/invalidScenario.generated.ts", typescript% Tazuna.Sim.InvalidScenario ++
      halting "InvalidScenario" (((groupSamples% Tazuna.Sim.InvalidScenario).filter (·.halts)).map (·.kind))),
   ("src/data/scenario.generated.ts",
    zod% Tazuna.Scenario Tazuna.Spec.Ref Tazuna.Scenario.Origin
      Tazuna.Scenario.Fact Tazuna.Scenario.ValueRef Tazuna.Scenario.Fill Tazuna.Scenario.Hole Tazuna.Scenario.Template
      Tazuna.Scenario.Line Tazuna.Scenario.SentRequest Tazuna.Scenario.EmittedEvent
      Tazuna.Scenario.Expectation Tazuna.Scenario.GivenRecord Tazuna.Scenario.Peer Tazuna.Scenario.PeerEntry
      Tazuna.Scenario.Given),
   ("src/data/fault.generated.ts", typescript% Tazuna.Service.Fault ++
      halting "Fault" (((groupSamples% Tazuna.Service.Fault).filter (·.halts)).map (·.kind))),
   ("src/data/bagOrderDependent.generated.ts", typescript% Tazuna.Explore.BagOrderDependent),
   ("src/data/choiceDependent.generated.ts",
    typescript% Tazuna.Explore.ChoiceDependent Tazuna.Explore.Difference Tazuna.Explore.Assigned),
   ("src/data/transitionRef.generated.ts",
    types% Tazuna.Spec.CallOutcome Tazuna.Spec.SendOutcome Tazuna.Spec.Trigger Tazuna.Spec.TransitionRef),
   ("src/data/step.generated.ts",
    types% Tazuna.Service.InstanceId Tazuna.Service.Requester Tazuna.Service.Received Tazuna.Service.Activity
      Tazuna.Service.StepName),
   ("src/data/trace.generated.ts",
    zod% Tazuna.Data.TraceLine Tazuna.Data.RejectionKind Tazuna.Data.Rejection Tazuna.Data.Answer ++ byCallerKinds),
   ("src/data/limits.generated.ts", limitsFile),
   ("src/spec/structure.generated.ts",
    zodType% Tazuna.Spec.Structure Tazuna.Data.RejectionKind Tazuna.Spec.Ref Tazuna.Spec.Activity
      Tazuna.Spec.Transition Tazuna.Spec.State Tazuna.Spec.ChartFields Tazuna.Spec.Reference
      Tazuna.Spec.Definition Tazuna.Spec.Contract Tazuna.Spec.ServiceInfo),
   ("test/lean/protocol.generated.ts",
    zodTypes% "../../src/" Tazuna.Service.Schema Tazuna.Service.Issue Tazuna.Service.CopyScope Tazuna.Service.Scope
      Tazuna.Service.Transition Tazuna.Service.Assignment Tazuna.Service.Extra Tazuna.Service.Emit
      Tazuna.Service.NextKeys Tazuna.Service.Keys Tazuna.Explore.Holder Tazuna.Explore.Access Tazuna.Verify.Part
      Tazuna.DiffTest.PairedService Tazuna.DiffTest.StepOrder Tazuna.DiffTest.Request Tazuna.DiffTest.Question
      Tazuna.DiffTest.Asked Tazuna.DiffTest.ItemKey Tazuna.DiffTest.Deadline Tazuna.DiffTest.Reply
      Tazuna.DiffTest.Replied)]

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
