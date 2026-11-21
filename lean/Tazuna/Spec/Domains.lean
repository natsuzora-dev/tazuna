import Tazuna.Spec.Structure

/-!
The values that explore writes into the lines it appends, from the domains that the spec's `explore` declares. treeOf
reads a schema's JSON Schema into a Tree: a node that a domain names takes the domain's values, and every other node
takes the values of its type when the type is finite. A leaf of an infinite type without a domain has no value, and
check reports it (Illegal.undeclaredDomain).
-/

namespace Tazuna.Spec.Domains

open Tazuna.Data Tazuna.Spec

mutual

/-- The values of a schema, as explore reads its JSON Schema with the declared domains. -/
inductive Tree where
  /-- A declared domain's values, or the values of a finite type: a constant, an enum, null, or a boolean. -/
  | listed (values : List Value)
  /-- The values of each option of a union or a type list. -/
  | union (options : Options)
  /-- The objects that hold each field with each of its values, and also leave out each field that is not required. -/
  | object (fields : Fields)
  /-- A leaf at `path` of an infinite type that no domain names. It has no value. -/
  | undeclared (path : List SchemaStep)

inductive Options where
  | nil
  | cons (option : Tree) (rest : Options)

inductive Fields where
  | nil
  | cons (name : String) (required : Bool) (tree : Tree) (rest : Fields)

end

instance : Inhabited Tree := ⟨.listed []⟩
instance : Inhabited Options := ⟨.nil⟩
instance : Inhabited Fields := ⟨.nil⟩

mutual

def Tree.values : Tree → List Value
  | .listed vs => vs
  | .union os => os.values
  | .object fs => fs.values.map .obj
  | .undeclared _ => []

def Options.values : Options → List Value
  | .nil => []
  | .cons t rest => t.values ++ rest.values

/-- The fields of each object, in field order: each value of the first field, then the first field left out. -/
def Fields.values : Fields → List (List (String × Value))
  | .nil => [[]]
  | .cons name required t rest =>
    (t.values.flatMap fun v => rest.values.map ((name, v) :: ·)) ++ (if required then [] else rest.values)

end

mutual

/-- The paths of the tree's leaves that no domain names. -/
def Tree.undeclaredPaths : Tree → List (List SchemaStep)
  | .listed _ => []
  | .union os => os.undeclaredPaths
  | .object fs => fs.undeclaredPaths
  | .undeclared path => [path]

def Options.undeclaredPaths : Options → List (List SchemaStep)
  | .nil => []
  | .cons t rest => t.undeclaredPaths ++ rest.undeclaredPaths

def Fields.undeclaredPaths : Fields → List (List SchemaStep)
  | .nil => []
  | .cons _ _ t rest => t.undeclaredPaths ++ rest.undeclaredPaths

end

mutual

/-- The values that a tree admits: each leaf's value lies in its domain or its finite type. -/
inductive Tree.Admits : Tree → Value → Prop
  | listed {vs : List Value} {v : Value} : v ∈ vs → Tree.Admits (.listed vs) v
  | union {os : Options} {v : Value} : Options.Admit os v → Tree.Admits (.union os) v
  | object {fs : Fields} {vs : List (String × Value)} : Fields.Admit fs vs → Tree.Admits (.object fs) (.obj vs)

inductive Options.Admit : Options → Value → Prop
  | head {t : Tree} {rest : Options} {v : Value} : Tree.Admits t v → Options.Admit (.cons t rest) v
  | tail {t : Tree} {rest : Options} {v : Value} : Options.Admit rest v → Options.Admit (.cons t rest) v

/-- The fields of an object that the trees admit, in field order; a field that is not required may be left out. -/
inductive Fields.Admit : Fields → List (String × Value) → Prop
  | nil : Fields.Admit .nil []
  | present {name : String} {required : Bool} {t : Tree} {rest : Fields} {v : Value} {vs : List (String × Value)} :
      Tree.Admits t v → Fields.Admit rest vs → Fields.Admit (.cons name required t rest) ((name, v) :: vs)
  | absent {name : String} {t : Tree} {rest : Fields} {vs : List (String × Value)} :
      Fields.Admit rest vs → Fields.Admit (.cons name false t rest) vs

end

/-- The values that the domains of `domains` declare for the node at `path` of `schema`: the first that names it. -/
def declared (domains : List Domain) (schema : Schema) (path : List SchemaStep) : Option (List Value) :=
  (domains.find? fun d => d.schema == schema && d.path == path).map (·.values)

/--
The tree of the JSON Schema `s` at `path`. A node that `declared` names takes its values. Otherwise a union and a type
list take each option's values, a constant and an enum their values, null itself, and a boolean false and true. An
object without other properties holds each property's values, and also leaves out each property that `required`
does not list, since its input type takes no value there (an optional field, or one with a default). Any other node
is undeclared: a string, a number, an array, a record, or a recursive reference.
-/
partial def treeOf (declared : List SchemaStep → Option (List Value)) (s : Value) (path : List SchemaStep) : Tree :=
  match declared path with
  | some vs => .listed vs
  | none =>
    match s.field? "anyOf", s.field? "oneOf", s.field? "const", s.field? "enum", s.field? "type" with
    | some (.arr options), _, _, _, _ | none, some (.arr options), _, _, _ => .union (union options.zipIdx)
    | none, none, some c, _, _ => .listed [c]
    | none, none, none, some (.arr values), _ => .listed values
    | none, none, none, _, some (.arr types) => .union (union (types.map (overlay s)).zipIdx)
    | none, none, none, _, some (.str "null") => .listed [.null]
    | none, none, none, _, some (.str "boolean") => .listed [.bool false, .bool true]
    | none, none, none, _, some (.str "object") =>
      match s.field? "additionalProperties", s.field? "properties" with
      | some (.obj _), _ | some (.bool true), _ => .undeclared path
      | _, some (.obj properties) => .object (fields properties)
      | _, _ => .listed [.obj []]
    | _, _, _, _, _ => .undeclared path
where
  overlay (s t : Value) : Value := match s with
    | .obj fields => .obj (fields.map fun (k, v) => (k, if k == "type" then t else v))
    | _ => s
  union : List (Value × Nat) → Options
    | [] => .nil
    | (o, j) :: rest => .cons (treeOf declared o (path ++ [.option j])) (union rest)
  required (k : String) : Bool := match s.field? "required" with
    | some (.arr names) => names.contains (.str k)
    | _ => false
  fields : List (String × Value) → Fields
    | [] => .nil
    | (k, p) :: rest => .cons k (required k) (treeOf declared p (path ++ [.field k])) (fields rest)

/--
The schemas whose values explore's moves for `service` carry, in some scenario: the input of each own command and
query; the output of each other service's command or query that an own definition sends, which an external peer
answers; the payload of each event of another service that the service receives, which an external peer emits; and
the payload of each control that an own screen offers as `any`. Which peers are external is the scenario's choice, so
every other service counts.
-/
def moveSchemas (s : Structure) (service : String) : List Schema :=
  let own := s.definitions.filter (·.service == service)
  let offersAny (c : Chart) (control : String) : Bool :=
    (c.offers ++ c.states.flatMap (·.offers)).any fun (k, o) => k == control && o matches .any
  (own.filterMap fun d => match d.body with
    | .command _ | .query _ => some (.input d.ref)
    | _ => none) ++
  ((s.requestsOf service).filterMap fun r =>
    if r.service == service then none else
    match s.body? r with
    | some (.command { output := some _, .. }) | some (.query { output := some _, .. }) => some (.output r)
    | _ => none) ++
  (s.receivesOf service).map .payload ++
  own.flatMap fun d => match d.body with
    | .screen c => c.controls.filterMap fun (k, x) => if x.isSome && offersAny c k then some (.control d.ref k) else none
    | _ => []

/-- The tree of `schema` under the domains of `explore`, or none when the structure has no such schema. -/
def schemaTree? (s : Structure) (explore : Explore) (schema : Schema) : Option Tree :=
  (s.schemaOf schema).map fun json => treeOf (declared explore.domains schema) json []

end Tazuna.Spec.Domains
