import Tazuna.Data.Canonical
import Tazuna.Data.UnionOptions
import Tazuna.Spec.Structure

/-!
The values that explore writes into the lines it appends, from the domains that the spec's `explore` declares. treeOf
reads a schema's JSON Schema into a Tree: a node that a domain names takes the domain's values, and every other node
takes the values of its type when the type is finite. A node of an infinite type without a domain makes the schema
undeclared, which check reports (Illegal.undeclaredDomain), and explore never enumerates.
-/

namespace Tazuna.Spec.Domains

open Tazuna.Data Tazuna.Spec

mutual

/-- The values of a schema, as explore reads its JSON Schema with the declared domains. -/
inductive Tree where
  /-- A declared domain's values, or the values of a finite type. -/
  | listed (values : List Value)
  /-- The values of each option of a union or a type list. -/
  | union (options : Options)
  /-- The objects that hold each field with each of its values, and also leave out each field that is not required. -/
  | object (fields : Fields)

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

/-- The values that a tree admits. -/
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

/-- How treeOf reads a node of a JSON Schema that no domain names: by the first keyword that decides it. -/
inductive Node where
  /-- `$ref` to the entry `name` of the root's `$defs`, which Zod writes for a schema registered with an id. -/
  | ref (name : String)
  /-- `anyOf`, which Zod writes for a union, or `oneOf`, for a discriminated union. -/
  | union (options : List Value)
  /-- A list of types: one option per type, each read with the node's other keywords (typed). -/
  | types (types : List Value)
  /-- A finite type, with its values: a constant, an enum, null, a boolean, or an object without properties. -/
  | finite (values : List Value)
  /-- An object with properties and without `additionalProperties`, with the names that `required` lists. -/
  | object (properties : List (String × Value)) (required : List Value)
  /-- A string, a number, an array, a record, a `$ref` that names no entry left, or a keyword of another shape. -/
  | undeclared
deriving Inhabited

/-- The node of type `t` with the other keywords of `s`. -/
def typed (s : Value) : Value → Node
  | .str "null" => .finite [.null]
  | .str "boolean" => .finite [.bool false, .bool true]
  | .str "object" =>
    match s.field? "additionalProperties", s.field? "properties" with
    | some (.obj _), _ | some (.bool true), _ => .undeclared
    | _, some (.obj properties) =>
      .object properties (match s.field? "required" with
        | some (.arr names) => names
        | _ => [])
    | _, _ => .finite [.obj []]
  | _ => .undeclared

def nodeOf (s : Value) : Node :=
  match s.field? "$ref", s.field? "anyOf", s.field? "oneOf", s.field? "const", s.field? "enum", s.field? "type" with
  | some (.str r), _, _, _, _, _ => match r.dropPrefix? "#/$defs/" with
    | some name => .ref name.toString
    | none => .undeclared
  | some _, _, _, _, _, _ => .undeclared
  | none, some (.arr options), _, _, _, _ => .union options
  | none, none, some (.arr options), _, _, _ => .union options
  | none, none, none, some c, _, _ => .finite [c]
  | none, none, none, none, some (.arr values), _ => .finite values
  | none, none, none, none, _, some (.arr types) => .types types
  | none, none, none, none, _, some t => typed s t
  | _, _, _, _, _, _ => .undeclared

/-- The entries of the root JSON Schema's `$defs`. -/
def defsOf (root : Value) : List (String × Value) :=
  match root.field? "$defs" with
  | some (.obj defs) => defs
  | _ => []

theorem nodeOf_union_lt {s : Value} {options : List Value} {o : Value} (h : nodeOf s = .union options)
    (ho : o ∈ options) : sizeOf o < sizeOf s := by
  have := List.sizeOf_lt_of_mem ho
  unfold nodeOf at h
  split at h
  · split at h <;> cases h
  all_goals first
    | (unfold typed at h; split at h <;> (try split at h) <;> cases h)
    | cases h
  all_goals
    rename_i hf
    have := Value.field?_lt hf
    simp only [Value.arr.sizeOf_spec] at *
    omega

theorem typed_object_lt {s t : Value} {properties : List (String × Value)} {required : List Value}
    {p : String × Value} (h : typed s t = .object properties required) (hp : p ∈ properties) :
    sizeOf p.2 < sizeOf s := by
  have := sizeOf_snd_lt hp
  unfold typed at h
  split at h <;> try cases h
  split at h <;> cases h
  rename_i hf
  have := Value.field?_lt hf
  simp only [Value.obj.sizeOf_spec] at *
  omega

theorem nodeOf_object_lt {s : Value} {properties : List (String × Value)} {required : List Value}
    {p : String × Value} (h : nodeOf s = .object properties required) (hp : p ∈ properties) :
    sizeOf p.2 < sizeOf s := by
  unfold nodeOf at h
  split at h
  · split at h <;> cases h
  all_goals first
    | cases h
    | exact typed_object_lt h hp

/-- The entries of `defs` but `name`'s. -/
def without (defs : List (String × Value)) (name : String) : List (String × Value) := defs.filter (·.1 != name)

theorem length_without_lt {defs : List (String × Value)} {name : String} {d : Value}
    (h : defs.lookup name = some d) : (without defs name).length < defs.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  induction defs with
  | nil => simp at h
  | cons x rest ih =>
    obtain ⟨k, v⟩ := x
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hk
      simp only [beq_iff_eq] at hk
      exact ⟨(k, v), List.mem_cons_self, by simp [hk]⟩
    · obtain ⟨y, hy, hn⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, hn⟩

/-- The paths of the nodes that no domain names and whose type is not finite. -/
abbrev Undeclared := List (List SchemaStep)

def Except.undeclared {α : Type} : Except Undeclared α → Undeclared
  | .error paths => paths
  | .ok _ => []

def options : List (Except Undeclared Tree) → Except Undeclared Options
  | [] => .ok .nil
  | r :: rest =>
    match r, options rest with
    | .ok t, .ok os => .ok (.cons t os)
    | .ok _, .error q => .error q
    | .error p, os => .error (p ++ Except.undeclared os)

def fields : List (String × Bool × Except Undeclared Tree) → Except Undeclared Fields
  | [] => .ok .nil
  | (name, required, r) :: rest =>
    match r, fields rest with
    | .ok t, .ok fs => .ok (.cons name required t fs)
    | .ok _, .error q => .error q
    | .error p, fs => .error (p ++ Except.undeclared fs)

/--
The tree of the JSON Schema `s` at `path`, whose `$ref`s name the entries of `defs`, or the paths of its nodes that no
domain names and whose type is not finite. A node that `declared` names takes its values. Otherwise nodeOf decides: a
`$ref` reads its entry with that entry left out of `defs`, so that a recursive reference is undeclared; a union and a
list of types take each option's values; a finite type takes its values; an object holds each property's values, and
also leaves out each property that `required` does not list, since its input type takes no value there (an optional
field, or one with a default).
-/
def treeOf (declared : List SchemaStep → Option (List Value)) (defs : List (String × Value)) (s : Value)
    (path : List SchemaStep) : Except Undeclared Tree :=
  match declared path with
  | some vs => .ok (.listed vs)
  | none =>
    match _h : nodeOf s with
    | .ref name =>
      match _hd : defs.lookup name with
      | some d => treeOf declared (without defs name) d path
      | none => .error [path]
    | .union os =>
      (options (os.zipIdx.attach.map fun x => treeOf declared defs x.1.1 (path ++ [.option x.1.2]))).map .union
    | .types ts =>
      (options (ts.zipIdx.map fun (t, j) =>
        match declared (path ++ [.option j]) with
        | some vs => .ok (.listed vs)
        | none =>
          match _ht : typed s t with
          | .finite vs => .ok (.listed vs)
          | .object ps required =>
            (fields (ps.attach.map fun x => (x.1.1, required.contains (.str x.1.1),
              treeOf declared defs x.1.2 (path ++ [.option j] ++ [.field x.1.1])))).map .object
          | _ => .error [path ++ [.option j]])).map .union
    | .finite vs => .ok (.listed vs)
    | .object ps required =>
      (fields (ps.attach.map fun x =>
        (x.1.1, required.contains (.str x.1.1), treeOf declared defs x.1.2 (path ++ [.field x.1.1])))).map .object
    | .undeclared => .error [path]
termination_by (defs.length, sizeOf s)
decreasing_by
  · exact Prod.Lex.left _ _ (length_without_lt _hd)
  · exact Prod.Lex.right _ (nodeOf_union_lt _h (List.fst_mem_of_mem_zipIdx (Subtype.property _)))
  · exact Prod.Lex.right _ (typed_object_lt _ht (Subtype.property _))
  · exact Prod.Lex.right _ (nodeOf_object_lt _h (Subtype.property _))

mutual

/--
The values that treeOf admits, stated by each node: a value of the domain that `declared` gives the node, of the entry
that a `$ref` names, of an option of a union or of a list of types, of a finite type, or an object whose fields are
admitted. No other value is admitted: a node of an infinite type without a domain admits none.
-/
inductive Admitted (declared : List SchemaStep → Option (List Value)) :
    List (String × Value) → Value → List SchemaStep → Value → Prop
  | declared {defs s path vs v} : declared path = some vs → v ∈ vs → Admitted declared defs s path v
  | ref {defs s path name d v} : declared path = none → nodeOf s = .ref name → defs.lookup name = some d →
      Admitted declared (without defs name) d path v → Admitted declared defs s path v
  | option {defs s path os o j v} : declared path = none → nodeOf s = .union os → (o, j) ∈ os.zipIdx →
      Admitted declared defs o (path ++ [.option j]) v → Admitted declared defs s path v
  | typeDeclared {defs s path ts t j vs v} : declared path = none → nodeOf s = .types ts → (t, j) ∈ ts.zipIdx →
      declared (path ++ [.option j]) = some vs → v ∈ vs → Admitted declared defs s path v
  | typeFinite {defs s path ts t j vs v} : declared path = none → nodeOf s = .types ts → (t, j) ∈ ts.zipIdx →
      declared (path ++ [.option j]) = none → typed s t = .finite vs → v ∈ vs → Admitted declared defs s path v
  | typeObject {defs s path ts t j ps required kvs} : declared path = none → nodeOf s = .types ts →
      (t, j) ∈ ts.zipIdx → declared (path ++ [.option j]) = none → typed s t = .object ps required →
      FieldsAdmitted declared defs ps required (path ++ [.option j]) kvs → Admitted declared defs s path (.obj kvs)
  | finite {defs s path vs v} : declared path = none → nodeOf s = .finite vs → v ∈ vs →
      Admitted declared defs s path v
  | object {defs s path ps required kvs} : declared path = none → nodeOf s = .object ps required →
      FieldsAdmitted declared defs ps required path kvs → Admitted declared defs s path (.obj kvs)

/-- The admitted fields of an object, in property order; a property that `required` does not list may be left out. -/
inductive FieldsAdmitted (declared : List SchemaStep → Option (List Value)) :
    List (String × Value) → List (String × Value) → List Value → List SchemaStep → List (String × Value) → Prop
  | nil {defs required path} : FieldsAdmitted declared defs [] required path []
  | present {defs k p ps required path v kvs} : Admitted declared defs p (path ++ [.field k]) v →
      FieldsAdmitted declared defs ps required path kvs →
      FieldsAdmitted declared defs ((k, p) :: ps) required path ((k, v) :: kvs)
  | absent {defs k p ps required path kvs} : required.contains (.str k) = false →
      FieldsAdmitted declared defs ps required path kvs →
      FieldsAdmitted declared defs ((k, p) :: ps) required path kvs

end

/-- The tree of a schema's root JSON Schema `json`, whose `$ref`s name the entries of its `$defs`. -/
def rootTree (declared : List SchemaStep → Option (List Value)) (json : Value) : Except Undeclared Tree :=
  treeOf declared (defsOf json) json []

/-- The values that the domains of `domains` declare for the node at `path` of `schema`. -/
def declared (domains : List Domain) (schema : Schema) (path : List SchemaStep) : Option (List Value) :=
  (domains.find? fun d => d.schema == schema && d.path == path).map (·.values)

/--
The schemas whose values explore's moves for `service` carry, in some scenario, each with its JSON Schema: the input of
each own command and query; the output of each other service's command or query that an own definition sends, which an
external peer answers; the payload of each event of another service that the service receives, which an external peer
emits; and the payload of each control that an own screen offers as `any`. Which peers are external is the scenario's
choice, so every other service counts.
-/
def moveSchemas (s : Structure) (service : String) : List (Schema × Value) :=
  let own := s.definitions.filter (·.service == service)
  let requested := s.requestsOf service
  let received := s.receivesOf service
  let offersAny (c : Chart) (control : String) : Bool :=
    (c.offers ++ c.states.flatMap (·.offers)).any fun (k, o) => k == control && o matches .any
  (own.filterMap fun d => match d.body with
    | .command c => some (.input d.ref, c.input)
    | .query q => some (.input d.ref, q.input)
    | _ => none) ++
  (s.definitions.filterMap fun d =>
    if d.service == service || !requested.contains d.ref then none else
    match d.body with
    | .command { output := some o, .. } | .query { output := some o, .. } => some (.output d.ref, o)
    | _ => none) ++
  (s.definitions.filterMap fun d =>
    if !received.contains d.ref then none else
    match d.body with
    | .event b => some (.payload d.ref, b.payload)
    | _ => none) ++
  own.flatMap fun d => match d.body with
    | .screen c => c.controls.filterMap fun (k, x) => match x with
      | some p => if offersAny c k then some (.control d.ref k, p) else none
      | none => none
    | _ => []

end Tazuna.Spec.Domains
