import Tazuna.Semantics.Value

/-! The structure rules: what a spec's structure must satisfy before any step runs. Each broken rule is one finding,
named after the definition that breaks it. -/

namespace Tazuna.Ir

/-- The structure rules. -/
inductive Illegal where
  /-- Two services or externals share a name, or two requests of one service, or two declarations of one external. -/
  | wireName
  /-- An external lists a command, query or event that another external owns. -/
  | owner
  /-- A subscription names an event no external declares and no service of the spec owns. -/
  | unknownSource
  /-- A table of the records has no `create` bound, or a `create` names no table. -/
  | creates
  /-- A type that crosses the wire holds a function or a fresh-id source. -/
  | wireType
  /-- A bound is negative. -/
  | bounds
deriving Repr, DecidableEq

namespace Illegal

def all : List Illegal := [wireName, owner, unknownSource, creates, wireType, bounds]

theorem mem_all (k : Illegal) : k ∈ all := by cases k <;> simp [all]

def name : Illegal → String
  | wireName => "wireName"
  | owner => "owner"
  | unknownSource => "unknownSource"
  | creates => "creates"
  | wireType => "wireType"
  | bounds => "bounds"

end Illegal

mutual
/-- Whether values of a type can cross the wire: data without functions or fresh-id sources. -/
def Ty.wire : Ty → Bool
  | .int | .str | .param _ | .date | .id => true
  | .list t | .bag t => Ty.wire t
  | .tuple ts => Ty.wires ts
  | .fn .. | .dsl .. => false
  | .adt _ _ vs => Ty.wiress vs
  | .table k v => Ty.wire k && Ty.wire v
def Ty.wires : List Ty → Bool
  | [] => true
  | t :: ts => Ty.wire t && Ty.wires ts
def Ty.wiress : List (List Ty) → Bool
  | [] => true
  | ts :: vs => Ty.wires ts && Ty.wiress vs
end

/-- The names that occur more than once. -/
def duplicates (names : List String) : List String :=
  (names.filter fun n => names.count n > 1).eraseDups

def DeclaredV.external : DeclaredV → String
  | .command e .. | .query e .. | .event e .. => e

def DeclaredV.name : DeclaredV → String
  | .command _ n .. | .query _ n .. | .event _ n .. => n

def DeclaredV.types : DeclaredV → List Ty
  | .command _ _ i o j => [i, o, j]
  | .query _ _ i o _ => [i, o]
  | .event _ _ e => [e]

/-- The labels of the fields of type `Table` in a records type. -/
def tableFields (T : List TypeDecl) : Ty → List String
  | .adt i _ _ => match T[i]? with
    | some d => (d.variants.flatMap (·.fields)).filterMap fun f => match f.ty with
      | .table .. => f.label
      | _ => none
    | none => []
  | _ => []

/-- Every broken structure rule of `s`, whose user types are `T`, with a message naming the definition. -/
def SpecV.illegal (T : List TypeDecl) (s : SpecV) : List (Illegal × String) :=
  let names := s.services.map (·.name) ++ s.externals.map (·.name)
  let topNames := (duplicates names).map fun n => (.wireName, s!"{n} names more than one service or external")
  let perService := s.services.flatMap fun v =>
    let requests := v.commands.map (·.name) ++ v.queries.map (·.name)
    let wireNames := (duplicates requests).map fun n => (Illegal.wireName, s!"{v.name}.{n} names more than one request")
    let wireTypes := ([("caller", v.caller), ("event", v.event)] ++
        v.commands.flatMap (fun c => [(c.name ++ " input", c.input), (c.name ++ " rejection", c.rejection)]) ++
        v.queries.flatMap (fun q => [(q.name ++ " input", q.input), (q.name ++ " output", q.output)])).filterMap
      fun (what, t) => if t.wire then none else some (Illegal.wireType, s!"{v.name}: the {what} type crosses the wire, so it holds no functions")
    let sources := v.subscribes.filterMap fun sub =>
      let declared := s.externals.any fun x => x.name == sub.source &&
        x.declared.any fun d => match d with
          | .event _ n _ => n == sub.name
          | _ => false
      if declared || s.services.any (·.name == sub.source) then none
      else some (Illegal.unknownSource, s!"{v.name} subscribes to {sub.source}.{sub.name}, which nothing declares")
    let tables := tableFields T v.records
    let bounded := v.bounds.creates.map (·.table)
    let creates := (tables.filter (!bounded.contains ·)).map (fun t =>
        (Illegal.creates, s!"{v.name}: the table {t} needs a create bound")) ++
      (bounded.filter (!tables.contains ·)).map fun t => (Illegal.creates, s!"{v.name}: create names {t}, which is no table of the records")
    let b := v.bounds
    let negative := ([("items", (b.items : Int)), ("cascade", b.cascade), ("steps", b.steps)] ++
        b.creates.map (fun c => ("create " ++ c.table, c.atMost))).filterMap
      fun (what, n) => if n < 0 then some (Illegal.bounds, s!"{v.name}: the {what} bound is negative") else none
    wireNames ++ wireTypes ++ sources ++ creates ++ negative
  let perExternal := s.externals.flatMap fun x =>
    let wireNames := (duplicates (x.declared.map (·.name))).map fun n =>
      (Illegal.wireName, s!"{x.name}.{n} is declared more than once")
    let owners := (x.declared.filter (·.external != x.name)).map fun d =>
      (Illegal.owner, s!"{x.name} lists {d.external}.{d.name}, which belongs to {d.external}")
    let wireTypes := (x.declared.filter fun d => !d.types.all Ty.wire).map fun d =>
      (Illegal.wireType, s!"{x.name}.{d.name}: its types cross the wire, so they hold no functions")
    wireNames ++ owners ++ wireTypes
  topNames ++ perService ++ perExternal

end Tazuna.Ir
