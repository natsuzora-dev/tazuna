import Tazuna.Linter

/-! Types after elaboration, the declarations of the types a program defines, and the types Lean owns. -/

namespace Tazuna.Ir

/-- The types of a spec's structure, which the `tazuna` module declares opaque: a spec builds their values with
built-ins and never looks inside them. `fresh` is the source of new ids a step hands a command. -/
inductive Dsl where
  | spec | service | command | query | machine | reaction | external
  | externalCommand | externalQuery | source | declared | effect | subscription
  | bounds | create | response | scenario | step | sender | fresh | closure | effectClosure
deriving Repr, DecidableEq, Inhabited

namespace Dsl

def all : List Dsl :=
  [.spec, .service, .command, .query, .machine, .reaction, .external, .externalCommand, .externalQuery,
   .source, .declared, .effect, .subscription, .bounds, .create, .response,
   .scenario, .step, .sender, .fresh, .closure, .effectClosure]

theorem mem_all (k : Dsl) : k ∈ all := by cases k <;> simp [all]

/-- The name the `tazuna` module gives the type, its type parameters, and what it is. -/
def decl : Dsl → String × List String × String
  | .spec => ("Spec", [], "The services a spec defines and the externals they talk to.")
  | .service => ("Service", [],
      "A service: its records, the events that write them, what it reacts to, and its scenarios.")
  | .command => ("Command", ["records", "event", "caller", "input", "rejection"],
      "A request that may write records through events.")
  | .query => ("Query", ["records", "caller", "input", "output"],
      "A request that answers from the records and writes nothing.")
  | .machine => ("Machine", ["records", "event"],
      "State kept per instance; an instance lives while its key is among the machine's instances.")
  | .reaction => ("Reaction", ["records", "event"], "Effects for each event, without state of its own.")
  | .external => ("External", [], "A service outside the spec, known by what it accepts and sends.")
  | .externalCommand => ("ExternalCommand", ["input", "output", "rejection"], "A command an external accepts.")
  | .externalQuery => ("ExternalQuery", ["input", "output"], "A query an external answers.")
  | .source => ("Source", ["event"], "Events of one name that an external or a service sends.")
  | .declared => ("Declared", ["records", "event", "caller"],
      "A command, query or source as its owner lists it: the service or external whose list holds it owns it. An external's list holds `Declared(Nil, Nil, Nil)`.")
  | .effect => ("Effect", ["event"],
      "A request to an external or to a command or query of the same service; its answer becomes events.")
  | .subscription => ("Subscription", ["event"], "Another service's event, received as one of this service's.")
  | .bounds => ("Bounds", ["records"], "How far checking goes.")
  | .create => ("Create", ["records"], "At most how many records one table of the records holds at any time.")
  | .response => ("Response", ["event"], "After one event, another within a time.")
  | .scenario => ("Scenario", ["records", "event", "caller"],
      "Steps a service takes from its initial records, compared with a snapshot.")
  | .step => ("Step", ["records", "event", "caller"], "One step of a scenario.")
  | .sender => ("Sender", [], "What sent a request: a machine instance or a reaction.")
  | .fresh => ("Fresh", [], "Where a command's new ids come from.")
  | .closure => ("Closure", ["function"],
      "A function a structure value keeps: Gleam writes it as the function type; Lean keeps its source.")
  | .effectClosure => ("EffectClosure", ["function"],
      "A function a structure value keeps that takes data and returns effects: Gleam writes it as the function type; Lean keeps its source.")

def name (k : Dsl) : String := (decl k).1

/-- Whether the type marks a function a structure value keeps, which Gleam writes as the function type. -/
def kept : Dsl → Bool
  | .closure | .effectClosure => true
  | _ => false

end Dsl

/-- A type after elaboration. `adt i args variants` is the `i`-th declaration of the program's type table at `args`,
carrying each variant's field types. No declaration refers to itself, directly or through others, so every type is a
finite tree and the meaning of a type follows its structure. `param k` is the `k`-th parameter of the declaration a
field type belongs to, or a rigid type variable of a generic function body. -/
inductive Ty where
  | int
  | str
  | list (t : Ty)
  | tuple (ts : List Ty)
  | fn (ps : List Ty) (r : Ty)
  | adt (i : Nat) (args : List Ty) (variants : List (List Ty))
  | param (k : Nat)
  /-- A multiset: equal when each value occurs as often in both. -/
  | bag (t : Ty)
  /-- A finite map: equal when it has the same keys, each with an equal value. -/
  | table (k v : Ty)
  /-- A day, without a calendar: only adding days and counting days between two dates have meaning. -/
  | date
  /-- An identifier a step makes fresh; only `==` has meaning. -/
  | id
  /-- A structure type at its type arguments. -/
  | dsl (k : Dsl) (args : List Ty)
deriving Repr, Inhabited

namespace Ty

mutual
/-- Evidence that two types are equal, when they are; elaboration casts terms with it. -/
def same : (a b : Ty) → Option (PLift (a = b))
  | .int, .int => some ⟨rfl⟩
  | .str, .str => some ⟨rfl⟩
  | .list a, .list b => (same a b).map fun ⟨h⟩ => ⟨h ▸ rfl⟩
  | .tuple a, .tuple b => (sames a b).map fun ⟨h⟩ => ⟨h ▸ rfl⟩
  | .fn a r, .fn b u => match sames a b, same r u with
    | some ⟨h⟩, some ⟨h'⟩ => some ⟨h ▸ h' ▸ rfl⟩
    | _, _ => none
  | .adt i a v, .adt j b w =>
    if hi : i = j then match sames a b, samess v w with
      | some ⟨h⟩, some ⟨h'⟩ => some ⟨hi ▸ h ▸ h' ▸ rfl⟩
      | _, _ => none
    else none
  | .param i, .param j => if h : i = j then some ⟨h ▸ rfl⟩ else none
  | .bag a, .bag b => (same a b).map fun ⟨h⟩ => ⟨h ▸ rfl⟩
  | .table k v, .table k' v' => match same k k', same v v' with
    | some ⟨h⟩, some ⟨h'⟩ => some ⟨h ▸ h' ▸ rfl⟩
    | _, _ => none
  | .date, .date => some ⟨rfl⟩
  | .id, .id => some ⟨rfl⟩
  | .dsl k a, .dsl k' b =>
    if hk : k = k' then (sames a b).map fun ⟨h⟩ => ⟨hk ▸ h ▸ rfl⟩ else none
  | _, _ => none
def sames : (a b : List Ty) → Option (PLift (a = b))
  | [], [] => some ⟨rfl⟩
  | x :: xs, y :: ys => match same x y, sames xs ys with
    | some ⟨h⟩, some ⟨h'⟩ => some ⟨h ▸ h' ▸ rfl⟩
    | _, _ => none
  | _, _ => none
def samess : (a b : List (List Ty)) → Option (PLift (a = b))
  | [], [] => some ⟨rfl⟩
  | x :: xs, y :: ys => match sames x y, samess xs ys with
    | some ⟨h⟩, some ⟨h'⟩ => some ⟨h ▸ h' ▸ rfl⟩
    | _, _ => none
  | _, _ => none
end

-- A type parameter past the arguments stays itself, unapplied.
set_option linter.tazuna.silentDefault false in
mutual
/-- Replaces `param k` with `args[k]`. -/
def inst (args : List Ty) : Ty → Ty
  | .int => .int
  | .str => .str
  | .list t => .list (inst args t)
  | .tuple ts => .tuple (insts args ts)
  | .fn ps r => .fn (insts args ps) (inst args r)
  | .adt i ts vs => .adt i (insts args ts) (instss args vs)
  | .param k => args[k]?.getD (.param k)
  | .bag t => .bag (inst args t)
  | .table k v => .table (inst args k) (inst args v)
  | .date => .date
  | .id => .id
  | .dsl k ts => .dsl k (insts args ts)
def insts (args : List Ty) : List Ty → List Ty
  | [] => []
  | t :: ts => inst args t :: insts args ts
def instss (args : List Ty) : List (List Ty) → List (List Ty)
  | [] => []
  | ts :: vs => insts args ts :: instss args vs
end

mutual
/-- Whether `==` may compare values of this type: Gleam compares functions by reference, which has no meaning here. -/
def comparable : Ty → Bool
  | .int | .str | .param _ | .date | .id => true
  | .list t | .bag t => comparable t
  | .table k v => comparable k && comparable v
  | .tuple ts => comparables ts
  | .adt _ _ vs => comparabless vs
  | .fn .. => false
  -- Structure values hold functions; a fresh-id source is a counter.
  | .dsl k _ => k == .fresh
def comparables : List Ty → Bool
  | [] => true
  | t :: ts => comparable t && comparables ts
def comparabless : List (List Ty) → Bool
  | [] => true
  | ts :: vs => comparables ts && comparabless vs
end

/-- Evidence that every variant has a field of type `ft` at index `k`, when it does. -/
def fieldAt (k : Nat) (ft : Ty) : (vs : List (List Ty)) → Option (PLift (∀ fs ∈ vs, fs[k]? = some ft))
  | [] => some ⟨by simp⟩
  | fs :: vs => match h : fs[k]?, fieldAt k ft vs with
    | some f, some ⟨p⟩ => (same f ft).map fun ⟨e⟩ => ⟨by
        intro gs hg
        cases hg with
        | head => rw [h, e]
        | tail _ hm => exact p gs hm⟩
    | _, _ => none

end Ty

structure Field where
  label : Option String
  ty : Ty
deriving Inhabited

structure Variant where
  name : String
  fields : List Field
deriving Inhabited

structure TypeDecl where
  name : String
  params : List String
  variants : List Variant
deriving Inhabited

/-- The atom Gleam's Erlang target names a variant by: the name in snake case, an underscore before each capital but
the first, as `HTTPError` becomes `h_t_t_p_error`. -/
def atomName (name : String) : String := String.ofList (go true name.toList)
where
  go : Bool → List Char → List Char
    | _, [] => []
    | first, c :: cs =>
      (if c.isUpper then (if first then [c.toLower] else ['_', c.toLower]) else [c]) ++ go false cs

namespace TypeDecl

/-- Each variant's field types at `args`: what `Ty.adt` carries. -/
def variantTys (d : TypeDecl) (args : List Ty) : List (List Ty) :=
  d.variants.map fun v => Ty.insts args (v.fields.map (·.ty))

/-- Gleam's record accessor: the field with this label sits at the same index with the same type in every variant. -/
def accessor (d : TypeDecl) (label : String) : Option (Nat × Ty) :=
  match d.variants with
  | [] => none
  | v :: _ => do
    let k ← v.fields.findIdx? (·.label == some label)
    let f ← v.fields[k]?
    if d.variants.all fun w => match w.fields[k]? with
        | some g => g.label == some label && (Ty.same g.ty f.ty).isSome
        | none => false
    then some (k, f.ty) else none

end TypeDecl

/-- The types every program has, at fixed indices: Lean owns them, the IR never declares them. -/
def prelude : List TypeDecl :=
  [ { name := "Bool", params := [], variants := [⟨"True", []⟩, ⟨"False", []⟩] },
    { name := "Nil", params := [], variants := [⟨"Nil", []⟩] },
    { name := "Result", params := ["a", "e"],
      variants := [⟨"Ok", [⟨none, .param 0⟩]⟩, ⟨"Error", [⟨none, .param 1⟩]⟩] },
    { name := "gleam/option.Option", params := ["a"],
      variants := [⟨"Some", [⟨none, .param 0⟩]⟩, ⟨"None", []⟩] },
    { name := "tazuna/bag.PickError", params := [], variants := [⟨"Empty", []⟩, ⟨"Tie", []⟩] },
    { name := "tazuna.Ctx", params := ["records", "input", "caller"],
      variants := [⟨"Ctx", [⟨some "records", .param 0⟩, ⟨some "input", .param 1⟩, ⟨some "caller", .param 2⟩,
        ⟨some "now", .int⟩, ⟨some "fresh", .dsl .fresh []⟩]⟩] },
    { name := "tazuna.Next", params := ["state"], variants := [⟨"Stay", []⟩, ⟨"Enter", [⟨none, .param 0⟩]⟩] },
    { name := "tazuna.Timer", params := ["state"],
      variants := [⟨"Timer", [⟨some "after", .int⟩, ⟨some "enter", .param 0⟩]⟩] },
    { name := "tazuna.MachineCtx", params := ["key", "state", "records"],
      variants := [⟨"MachineCtx", [⟨some "key", .param 0⟩, ⟨some "state", .param 1⟩, ⟨some "records", .param 2⟩,
        ⟨some "now", .int⟩]⟩] },
    { name := "tazuna.ReactionCtx", params := ["records"],
      variants := [⟨"ReactionCtx", [⟨some "records", .param 0⟩, ⟨some "now", .int⟩]⟩] },
    { name := "tazuna.QueryCtx", params := ["records", "input", "caller"],
      variants := [⟨"QueryCtx", [⟨some "records", .param 0⟩, ⟨some "input", .param 1⟩, ⟨some "caller", .param 2⟩,
        ⟨some "now", .int⟩]⟩] } ]

def Ty.bool : Ty := .adt 0 [] [[], []]
def Ty.nil : Ty := .adt 1 [] [[]]
def Ty.spec : Ty := .dsl .spec []
def Ty.pickError : Ty := .adt 4 [] [[], []]
def Ty.result (a e : Ty) : Ty := .adt 2 [a, e] [[a], [e]]
def Ty.option (a : Ty) : Ty := .adt 3 [a] [[a], []]
def Ty.ctx (r i c : Ty) : Ty := .adt 5 [r, i, c] [[r, i, c, .int, .dsl .fresh []]]
def Ty.next (s : Ty) : Ty := .adt 6 [s] [[], [s]]
def Ty.timer (s : Ty) : Ty := .adt 7 [s] [[.int, s]]
/-- What a machine's functions see of one instance: its key and state, the records, and the time. -/
def Ty.machineCtx (k s r : Ty) : Ty := .adt 8 [k, s, r] [[k, s, r, .int]]
/-- What a reaction sees: the records and the time. -/
def Ty.reactionCtx (r : Ty) : Ty := .adt 9 [r] [[r, .int]]
/-- What a query's `resolve` sees: a command's context without the source of fresh ids, since a query makes none. -/
def Ty.queryCtx (r i c : Ty) : Ty := .adt 10 [r, i, c] [[r, i, c, .int]]
/-- Named rules, as `invariants`, `accepts` and `ensures` return them. -/
def Ty.rules : Ty := .list (.tuple [.str, .bool])

mutual
/-- Whether a type is data: it holds no structure value, so it means the same at every level. -/
def Ty.isData : Ty → Bool
  | .list t | .bag t => Ty.isData t
  | .tuple ts => Ty.isDatas ts
  | .fn ps r => Ty.isDatas ps && Ty.isData r
  | .adt _ _ vs => Ty.isDatass vs
  | .table k v => Ty.isData k && Ty.isData v
  | .dsl k _ => k == .fresh
  | .int | .str | .param _ | .date | .id => true
def Ty.isDatas : List Ty → Bool
  | [] => true
  | t :: ts => Ty.isData t && Ty.isDatas ts
def Ty.isDatass : List (List Ty) → Bool
  | [] => true
  | ts :: vs => Ty.isDatas ts && Ty.isDatass vs
end


/-- The prelude's types at fixed indices are the ones the helpers above name. -/
example : prelude[0]?.map (fun d => Ty.adt 0 [] (d.variantTys [])) = some Ty.bool := rfl
example : prelude[1]?.map (fun d => Ty.adt 1 [] (d.variantTys [])) = some Ty.nil := rfl
example : prelude[4]?.map (fun d => Ty.adt 4 [] (d.variantTys [])) = some Ty.pickError := rfl
example (r i c : Ty) : prelude[5]?.map (fun d => Ty.adt 5 [r, i, c] (d.variantTys [r, i, c])) = some (Ty.ctx r i c) := rfl
example (s : Ty) : prelude[6]?.map (fun d => Ty.adt 6 [s] (d.variantTys [s])) = some (Ty.next s) := rfl
example (s : Ty) : prelude[7]?.map (fun d => Ty.adt 7 [s] (d.variantTys [s])) = some (Ty.timer s) := rfl
example (k s r : Ty) : prelude[8]?.map (fun d => Ty.adt 8 [k, s, r] (d.variantTys [k, s, r])) =
  some (Ty.machineCtx k s r) := rfl
example (r : Ty) : prelude[9]?.map (fun d => Ty.adt 9 [r] (d.variantTys [r])) = some (Ty.reactionCtx r) := rfl
example (r i c : Ty) : prelude[10]?.map (fun d => Ty.adt 10 [r, i, c] (d.variantTys [r, i, c])) =
  some (Ty.queryCtx r i c) := rfl
example (a e : Ty) : prelude[2]?.map (fun d => Ty.adt 2 [a, e] (d.variantTys [a, e])) = some (Ty.result a e) := rfl
example (a : Ty) : prelude[3]?.map (fun d => Ty.adt 3 [a] (d.variantTys [a])) = some (Ty.option a) := rfl

end Tazuna.Ir
