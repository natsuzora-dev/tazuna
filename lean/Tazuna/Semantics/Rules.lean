import Tazuna.Semantics.Eval
import Tazuna.Semantics.Order

/-! The structure rules: what a spec's structure must satisfy before any step runs. Each broken rule is one finding,
named after the definition that breaks it. -/

namespace Tazuna.Ir

/-- The structure rules. -/
inductive Illegal where
  /-- Two services or externals share a name, or two commands or queries of one service, or two entries of one
  external. -/
  | wireName
  /-- A service declares an external's command or query, or an external a service's; or two owners declare the same
  handle (same kind, name and types). -/
  | owner
  /-- A subscription names a source that no service or external lists with that name and event type. -/
  | unknownSource
  /-- A table field of the records has no `create` bound or more than one, or a `create` reads no table field. -/
  | creates
  /-- A type that crosses the wire holds a function or a fresh-id source. -/
  | wireType
  /-- The records type or a machine's state type holds a function or a fresh-id source: the state is durable data, so
  every value of it can be written down, as a wire value can. -/
  | stateType
  /-- A bound is negative. -/
  | bounds
  /-- A scenario step sends a request its service does not declare, two scenarios of a service share a name, or a
  scenario's name is no file name. -/
  | scenario
  /-- A command's rejection type is neither a custom type nor Nil: a rejection names its reason in a type of the
  spec's own. -/
  | rejection
  /-- A machine's instance key type has no order the solver can encode (`Ty.orderable`): the canonical order of the
  keys decides which instance reacts, starts and fires first, so the step encoding must compare keys. -/
  | machineKey
  /-- The program makes an external command or query handle that no external declares with its name and types: an
  effect may request only what an external declares. -/
  | unknownHandle
  /-- The program makes a command, query, external command or external query handle whose name is no string literal:
  a wire name is written once where it is defined, so check and the step encoding see which request a handle names. -/
  | handleName
  /-- A table inside the stored state, a type that crosses the wire or the values a kept function captures has a key
  that is no plain value (`Ty.plain`): an entry is found by comparing keys, which the solver does on plain values. -/
  | tableKey
deriving Repr, DecidableEq

namespace Illegal

def all : List Illegal :=
  [wireName, owner, unknownSource, creates, wireType, stateType, bounds, scenario, rejection, machineKey, unknownHandle,
    handleName, tableKey]

theorem mem_all (k : Illegal) : k ∈ all := by cases k <;> simp [all]

def name : Illegal → String
  | wireName => "wireName"
  | owner => "owner"
  | unknownSource => "unknownSource"
  | creates => "creates"
  | wireType => "wireType"
  | stateType => "stateType"
  | bounds => "bounds"
  | scenario => "scenario"
  | rejection => "rejection"
  | machineKey => "machineKey"
  | unknownHandle => "unknownHandle"
  | handleName => "handleName"
  | tableKey => "tableKey"

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

mutual
/-- Whether the solver compares values of a type by terms (`Tazuna.Smt.ordT`): Ints, dates, strings and ids, Bool and
enumerations, and tuples and one-variant records of such types. -/
def Ty.orderable : Ty → Bool
  | .int | .date | .str | .id => true
  | .tuple ts => Ty.orderables ts
  | .adt 0 _ [[], []] => true
  | .adt (_ + 1) _ [fs] => Ty.orderables fs
  | .adt (_ + 1) _ vs => vs.all (·.isEmpty)
  | _ => false
def Ty.orderables : List Ty → Bool
  | [] => true
  | t :: ts => Ty.orderable t && Ty.orderables ts
end

mutual
/-- Whether `==` on the type is equality of values: no list, bag, table, function or type parameter inside. -/
def Ty.plain : Ty → Bool
  | .int | .str | .date | .id => true
  | .tuple ts => Ty.plains ts
  | .adt _ _ vs => Ty.plainss vs
  | _ => false
def Ty.plains : List Ty → Bool
  | [] => true
  | t :: ts => Ty.plain t && Ty.plains ts
def Ty.plainss : List (List Ty) → Bool
  | [] => true
  | ts :: vs => Ty.plains ts && Ty.plainss vs
end

mutual
/-- Whether every table inside a value of the type has a plain key (`Ty.plain`). -/
def Ty.plainKeys : Ty → Bool
  | .list t | .bag t => Ty.plainKeys t
  | .tuple ts => Ty.plainKeyss ts
  | .adt _ _ vs => Ty.plainKeysss vs
  | .table k v => Ty.plain k && Ty.plainKeys v
  | _ => true
def Ty.plainKeyss : List Ty → Bool
  | [] => true
  | t :: ts => Ty.plainKeys t && Ty.plainKeyss ts
def Ty.plainKeysss : List (List Ty) → Bool
  | [] => true
  | ts :: vs => Ty.plainKeyss ts && Ty.plainKeysss vs
end

mutual
theorem Ty.beq_plain : (t : Ty) → t.plain = true → (x y : t.den0) → ((Ty.semWith Dsl.base t).2 x y = true ↔ x = y)
  | .int, _, x, y => beq_iff_eq (α := Int) (a := x) (b := y)
  | .str, _, x, y => beq_iff_eq (α := String) (a := x) (b := y)
  | .date, _, x, y => beq_iff_eq (α := Int) (a := x) (b := y)
  | .id, _, x, y => ⟨fun h => @of_decide_eq_true _ (instDecidableEqIdV x y) h,
      fun h => @decide_eq_true _ (instDecidableEqIdV x y) h⟩
  | .tuple ts, h, x, y => Ty.beq_plains ts h x y
  | .adt _ _ vs, h, x, y => Ty.beq_plainss vs h x y
theorem Ty.beq_plains : (ts : List Ty) → Ty.plains ts = true → (x y : (Ty.semsWith Dsl.base ts).1) →
    ((Ty.semsWith Dsl.base ts).2 x y = true ↔ x = y)
  | [], _, (), () => by simp [Ty.semsWith]
  | t :: ts, h, (a, as), (b, bs) => by
    simp only [Ty.plains, Bool.and_eq_true] at h
    have e1 := Ty.beq_plain t h.1 a b
    have e2 := Ty.beq_plains ts h.2 as bs
    show ((Ty.semWith Dsl.base t).2 a b && (Ty.semsWith Dsl.base ts).2 as bs) = true ↔ _
    constructor
    · intro hh
      simp only [Bool.and_eq_true] at hh
      obtain rfl := e1.1 hh.1
      obtain rfl := e2.1 hh.2
      rfl
    · intro hh
      cases hh
      simp [e1.2 rfl, e2.2 rfl]
theorem Ty.beq_plainss : (vs : List (List Ty)) → Ty.plainss vs = true → (x y : (Ty.semAltsWith Dsl.base vs).1) →
    ((Ty.semAltsWith Dsl.base vs).2 x y = true ↔ x = y)
  | [], _, x, _ => nomatch x
  | ts :: vs, h, x, y => by
    simp only [Ty.plainss, Bool.and_eq_true] at h
    rcases x with a | a <;> rcases y with b | b
    · refine (Ty.beq_plains ts h.1 a b).trans ⟨fun e => e ▸ rfl, fun e => ?_⟩
      cases e; rfl
    · exact ⟨fun e => (nomatch e), fun e => by cases e⟩
    · exact ⟨fun e => (nomatch e), fun e => by cases e⟩
    · refine (Ty.beq_plainss vs h.2 a b).trans ⟨fun e => e ▸ rfl, fun e => ?_⟩
      cases e; rfl
end

mutual
theorem Ty.plain_of_orderable : (t : Ty) → t.orderable = true → t.plain = true
  | .int, _ | .date, _ | .str, _ | .id, _ => rfl
  | .tuple ts, h => Ty.plains_of_orderables ts h
  | .adt 0 _ vs, h => by
    rcases vs with _ | ⟨_ | ⟨_, _⟩, _ | ⟨_ | ⟨_, _⟩, _ | ⟨_, _⟩⟩⟩ <;> simp_all [Ty.orderable, Ty.plain, Ty.plainss, Ty.plains]
  | .adt (_ + 1) _ vs, h => by
    rcases vs with _ | ⟨fs, _ | ⟨gs, ws⟩⟩
    · rfl
    · simp only [Ty.orderable] at h
      simp [Ty.plain, Ty.plainss, Ty.plains_of_orderables fs h]
    · simp only [Ty.orderable, List.all_cons, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true] at h
      obtain ⟨rfl, rfl, hw⟩ := h
      simp only [Ty.plain, Ty.plainss, Ty.plains, Bool.true_and]
      induction ws with
      | nil => rfl
      | cons w ws ih =>
        rw [hw w (by simp)]
        exact ih fun x hx => hw x (by simp [hx])
  | .list _, h | .bag _, h | .table .., h | .fn .., h | .param _, h | .dsl .., h => by simp [Ty.orderable] at h
theorem Ty.plains_of_orderables : (ts : List Ty) → Ty.orderables ts = true → Ty.plains ts = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Ty.orderables, Bool.and_eq_true] at h
    simp [Ty.plains, Ty.plain_of_orderable t h.1, Ty.plains_of_orderables ts h.2]
end

/-- The names that occur more than once. -/
def duplicates (names : List String) : List String :=
  (names.filter fun n => names.count n > 1).eraseDups

def DeclaredV.name : DeclaredV → String
  | .command _ _ _ x => x.name
  | .query _ _ x => x.name
  | .externalCommand n .. | .externalQuery n .. | .source n _ => n

/-- What kind of handle the entry is, as messages name it. -/
def DeclaredV.kind : DeclaredV → String
  | .command .. => "command"
  | .query .. => "query"
  | .externalCommand .. => "external command"
  | .externalQuery .. => "external query"
  | .source .. => "source"

/-- The types that, with the kind and name, make an entry the handle it is. -/
def DeclaredV.types : DeclaredV → List Ty
  | .command r e c x => [r, e, c, x.input, x.rejection]
  | .query r c x => [r, c, x.input, x.output]
  | .externalCommand _ i o j => [i, o, j]
  | .externalQuery _ i o _ => [i, o]
  | .source _ t => [t]

/-- The types that cross the wire when the handle is used. -/
def DeclaredV.wireTypes : DeclaredV → List Ty
  | .command _ _ _ x => [x.input, x.rejection]
  | .query _ _ x => [x.input, x.output]
  | d => d.types

/-- Whether two entries are one handle. -/
def DeclaredV.same (a b : DeclaredV) : Bool :=
  a.kind == b.kind && a.name == b.name && (Ty.sames a.types b.types).isSome

/-- A custom type of the spec's own, or Nil: what a rejection may be. -/
def Ty.customOrNil : Ty → Bool
  | .adt i _ _ => i == 1 || prelude.length ≤ i
  | _ => false

mutual
/-- Some value of a data type, when the type has one. -/
def Ty.default? : (t : Ty) → Option t.den0
  | .int => Option.some (0 : Int)
  | .str => Option.some ""
  | .list _ | .bag _ => Option.some []
  | .tuple ts => Ty.defaults? ts
  | .fn _ r => (Ty.default? r).map fun d _ => d
  | .adt _ _ vs => Ty.defaultAlt? vs
  | .param _ => Option.some ()
  | .table _ _ => Option.some ⟨[], .nil⟩
  | .date => Option.some (0 : Int)
  | .id => Option.some (IdV.fresh 0 0)
  | .dsl k _ => by cases k <;> first | exact Option.some (0 : Nat) | exact Option.some ()
def Ty.defaults? : (ts : List Ty) → Option (Ty.semsWith Dsl.base ts).1
  | [] => Option.some ()
  | t :: ts => do pure (← Ty.default? t, ← Ty.defaults? ts)
def Ty.defaultAlt? : (vs : List (List Ty)) → Option (Ty.semAltsWith Dsl.base vs).1
  | [] => Option.none
  | fs :: vs => match Ty.defaults? fs with
    | Option.some x => Option.some (.inl x)
    | Option.none => (Ty.defaultAlt? vs).map .inr
end

/-- Fields with defaults, except field `k`, which is a table of one entry. -/
def probeFields : (fs : List Ty) → Nat → Option (Ty.semsWith Dsl.base fs).1
  | [], _ => none
  | .table kt vt :: fs, 0 => do
    let entry : kt.den0 × vt.den0 := (← Ty.default? kt, ← Ty.default? vt)
    pure (⟨[entry], List.pairwise_singleton _ _⟩, ← Ty.defaults? fs)
  | _ :: _, 0 => none
  | f :: fs, k + 1 => do pure (← Ty.default? f, ← probeFields fs k)

/-- A value of variant `i` whose only nonempty table is its field `k`. -/
def probeAlts : (vs : List (List Ty)) → Nat → Nat → Option (Ty.semAltsWith Dsl.base vs).1
  | [], _, _ => none
  | fs :: _, 0, k => (probeFields fs k).map .inl
  | _ :: vs, i + 1, k => (probeAlts vs i k).map .inr

-- Probe labels for messages: a field without a label is named by its position.
set_option linter.tazuna.silentDefault false in
/-- The table fields of a records type, each with its label and a records value whose only nonempty table it is. A
table whose key or value type has no value never holds an entry, so it has no probe. -/
def tableProbes (T : List TypeDecl) : (r : Ty) → List (String × r.den0)
  | .adt i _ vs =>
    let decl := (T[i]?.map (·.variants)).getD []
    (vs.zipIdx.flatMap fun (fs, vi) => fs.zipIdx.filterMap fun (f, fi) => match f with
      | .table .. => (probeAlts vs vi fi).map fun x =>
        (((decl[vi]?.bind (·.fields[fi]?)).bind (·.label)).getD s!"{fi}", x)
      | _ => none)
  | _ => []

/-- The labels of the table fields a create reads: those whose probe makes its table nonempty. -/
def CreateV.reads {r : Ty} (c : CreateV r) (probes : List (String × r.den0)) : List String :=
  probes.filterMap fun (label, x) => if (c.table.fn (x, ())).1.isEmpty then none else some label

/-- A command, query, external command or external query handle the program makes: its kind as `DeclaredV.kind` names
it, its name when the program writes it as a string literal, and its types. -/
structure HandleSite where
  kind : String
  name : Option String
  types : List Ty

def _root_.Tazuna.Ir.Expr.lit? {G Γ : List Ty} {t : Ty} : Expr G Γ t → Option String
  | .str s => some s
  | _ => none

/-- The handle `command`, `query`, `external_command` or `external_query` makes with the name `name`. -/
def handleOf (p : Prim) (ts : List Ty) (name : Option String) : Option HandleSite :=
  match p with
  | .externalCommand => some ⟨"external command", name, ts⟩
  | .externalQuery => some ⟨"external query", name, ts⟩
  | .command => some ⟨"command", name, ts⟩
  | .query => some ⟨"query", name, ts⟩
  | _ => none

/-- The handle a call makes, when it calls `command`, `query`, `external_command` or `external_query`. -/
def handleAt {G Γ : List Ty} {ps : List Ty} {r : Ty} (f : Expr G Γ (.fn ps r)) (args : Exprs G Γ ps) : Option HandleSite :=
  let name : Option String := match args with
    | .cons e _ => e.lit?
    | .nil => none
  match f with
  | .prim p ts _ => handleOf p ts name
  | _ => none

section
variable {G : List Ty}

mutual
/-- The handles an expression makes, nested functions included. -/
def Expr.handles {Γ : List Ty} {t : Ty} : Expr G Γ t → List HandleSite
  | .int _ | .str _ | .var _ | .global _ => []
  -- A handle built-in passed as a value names whatever its caller gives it, which check cannot see.
  | .prim p ts _ => (handleOf p ts none).toList
  | .ctor _ es | .tuple es => Exprs.handles es
  | .field _ _ _ e | .index e _ | .not e | .neg e | .lam e => Expr.handles e
  | .update e p => Expr.handles e ++ Patch.handles p
  | .call f args => match handleAt f args with
    | some h => h :: Exprs.handles args
    | none => Expr.handles f ++ Exprs.handles args
  | .let_ e body | .bin _ e body => Expr.handles e ++ Expr.handles body
  | .case e cs _ => Expr.handles e ++ Clauses.handles cs
  | .list items => Items.handles items
  | .close _ env _ _ body | .closeEffect _ env _ _ body => Exprs.handles env ++ Expr.handles body
def Exprs.handles {Γ ts : List Ty} : Exprs G Γ ts → List HandleSite
  | .nil => []
  | .cons e es => Expr.handles e ++ Exprs.handles es
def Items.handles {Γ : List Ty} {t : Ty} : Items G Γ t → List HandleSite
  | .nil => []
  | .cons e es => Expr.handles e ++ Items.handles es
def Patch.handles {Γ ts : List Ty} : Patch G Γ ts → List HandleSite
  | .nil => []
  | .keep rest => Patch.handles rest
  | .set e rest => Expr.handles e ++ Patch.handles rest
def Clauses.handles {Γ : List Ty} {t r : Ty} {sh : List Shape} : Clauses G Γ t r sh → List HandleSite
  | .nil => []
  | .cons _ body rest => Expr.handles body ++ Clauses.handles rest
  | .guarded _ g body rest => Expr.handles g ++ Expr.handles body ++ Clauses.handles rest
end

end

/-- Every handle a program makes. -/
def Defs.handles : {G : List Ty} → Defs G → List HandleSite
  | [], .nil => []
  | _ :: _, .snoc defs _ body => defs.handles ++ body.handles

def tableKeyAdvice : String :=
  "the solver finds an entry by comparing keys, so make the key Int, String, Date, Id, or a custom type or tuple of these"

/-- Every broken structure rule of `s`, whose user types are `T` and whose program makes `handles` and kept functions
capturing values of the types `captures`, with a message naming the definition. -/
def SpecV.illegal (T : List TypeDecl) (s : SpecV) (handles : List HandleSite) (captures : List (SiteId × List Ty)) :
    List (Illegal × String) :=
  let names := s.services.map (·.name) ++ s.externals.map (·.name)
  let topNames := (duplicates names).map fun n => (.wireName, s!"{n} names more than one service or external")
  let entries : List (String × DeclaredV) := s.services.flatMap (fun v => v.declares.map (v.name, ·)) ++
    s.externals.flatMap fun x => x.declares.map (x.name, ·)
  let sharedOwners := (entries.zipIdx.filterMap fun ((o, d), k) =>
    match (entries.take k).find? fun (o', d') => o' != o && d.same d' with
    | some (o', _) => some (Illegal.owner, s!"{o'} and {o} both declare the {d.kind} {d.name}")
    | none => none)
  let sources := s.services.flatMap (fun v => v.sources.map fun (n, t) => (n, t)) ++
    s.externals.flatMap fun x => x.declares.filterMap fun | .source n t => some (n, t) | _ => none
  let perService := s.services.flatMap fun v =>
    let requests := v.commands.map (·.name) ++ v.queries.map (·.name)
    let wireNames := (duplicates requests ++ duplicates (v.sources.map (·.1))).map fun n =>
      (Illegal.wireName, s!"{v.name}.{n} names more than one request or source")
    let owners := v.declares.filterMap fun
      | .externalCommand n .. | .externalQuery n .. =>
        some (Illegal.owner, s!"{v.name} declares {n}, an external's command or query")
      | _ => none
    let wireList := [("caller", v.caller), ("event", v.event)] ++
        v.commands.flatMap (fun c => [(c.name ++ " input", c.input), (c.name ++ " rejection", c.rejection)]) ++
        v.queries.flatMap (fun q => [(q.name ++ " input", q.input), (q.name ++ " output", q.output)]) ++
        v.sources.map (fun (n, t) => (n ++ " event", t))
    let wireTypes := wireList.filterMap
      fun (what, t) => if t.wire then none else some (Illegal.wireType, s!"{v.name}: the {what} type crosses the wire, so it holds no functions")
    let stateList := ("records", v.records) :: v.machines.map fun m => (m.name ++ " state", m.state)
    let stateTypes := stateList.filterMap
      fun (what, t) => if t.wire then none else some (Illegal.stateType, s!"{v.name}: the {what} type is stored state, so it holds no functions")
    let unknown := v.subscribes.filterMap fun sub =>
      if sources.any fun (n, t) => n == sub.name && (Ty.same t sub.event).isSome then none
      else some (Illegal.unknownSource, s!"{v.name} subscribes to the source {sub.name}, which no service or external declares with its event type")
    let rejections := v.commands.filterMap fun c => if c.rejection.customOrNil then none else
      some (Illegal.rejection, s!"{v.name}.{c.name}: the rejection type is no custom type or Nil")
    let keys := v.machines.filterMap fun m => if m.key.orderable && m.key.ordered T then none else
      some (Illegal.machineKey, s!"{v.name}.{m.name}: the instance key type has no canonical order the solver can compare; use Int, String, Date, Id, Bool, an enumeration, or a tuple or one-variant record of these")
    let probes := tableProbes T v.records
    let reads := v.bounds.creates.map (·.reads probes)
    let creates := (probes.filterMap fun (t, _) => match (reads.filter (·.contains t)).length with
        | 0 => some (Illegal.creates, s!"{v.name}: the table {t} needs a create bound")
        | 1 => none
        | _ => some (Illegal.creates, s!"{v.name}: the table {t} has more than one create bound")) ++
      ((reads.filter (·.isEmpty)).map fun _ =>
        (Illegal.creates, s!"{v.name}: a create bound reads no table field of the records"))
    let b := v.bounds
    let negative := ([("items", (b.items : Int)), ("cascade", b.cascade), ("steps", b.steps)] ++
        (v.bounds.creates.zip reads).map (fun (c, ts) => ("create " ++ ", ".intercalate ts, c.atMost))).filterMap
      fun (what, n) => if n < 0 then some (Illegal.bounds, s!"{v.name}: the {what} bound is negative") else none
    let scenarioNames := (duplicates (v.scenarios.map (·.name))).map fun n =>
      (Illegal.scenario, s!"{v.name}/{n} names more than one scenario")
    let perScenario := v.scenarios.flatMap fun sc =>
      let here := s!"the scenario {v.name}/{sc.name}"
      let fileName := if sc.name.isEmpty || sc.name.contains '/' || sc.name.startsWith "." then
          [(Illegal.scenario, s!"{here} has a name that is no file name")] else []
      let steps := sc.steps.zipIdx.filterMap fun (st, k) =>
        let unlisted (kind n : String) := some (Illegal.scenario, s!"{here}: step {k + 1} sends the {kind} {n}, which {v.name} does not declare")
        match st with
        | .command x _ _ _ =>
          if v.commands.any fun c => c.name == x.name && (Ty.same c.input x.input).isSome &&
            (Ty.same c.rejection x.rejection).isSome then none else unlisted "command" x.name
        | .query x _ _ =>
          if v.queries.any fun q => q.name == x.name && (Ty.same q.input x.input).isSome &&
            (Ty.same q.output x.output).isSome then none else unlisted "query" x.name
        | _ => none
      fileName ++ steps
    let tableKeys := (wireList ++ stateList ++ v.machines.map fun m => (m.name ++ " key", m.key)).filterMap
      fun (what, t) => if t.plainKeys then none else
        some (Illegal.tableKey, s!"{v.name}: the {what} type holds a table whose key is no plain value; {tableKeyAdvice}")
    wireNames ++ owners ++ wireTypes ++ stateTypes ++ unknown ++ rejections ++ keys ++ creates ++ negative ++ scenarioNames ++ perScenario ++
      tableKeys
  let perExternal := s.externals.flatMap fun x =>
    let all := x.declares
    let wireNames := (duplicates (all.map (·.name))).map fun n =>
      (Illegal.wireName, s!"{x.name}.{n} is declared more than once")
    let owners := all.filterMap fun
      | .command _ _ _ c => some (Illegal.owner, s!"{x.name} declares {c.name}, a service's command")
      | .query _ _ q => some (Illegal.owner, s!"{x.name} declares {q.name}, a service's query")
      | _ => none
    let wireTypes := (all.filter fun d => !d.wireTypes.all Ty.wire).map fun d =>
      (Illegal.wireType, s!"{x.name}.{d.name}: its types cross the wire, so they hold no functions")
    let rejections := all.filterMap fun
      | .externalCommand n _ _ j => if j.customOrNil then none else
        some (Illegal.rejection, s!"{x.name}.{n}: the rejection type is no custom type or Nil")
      | _ => none
    let tableKeys := (all.filter fun d => !d.wireTypes.all Ty.plainKeys).map fun d =>
      (Illegal.tableKey, s!"{x.name}.{d.name}: its types hold a table whose key is no plain value; {tableKeyAdvice}")
    wireNames ++ owners ++ wireTypes ++ rejections ++ tableKeys
  -- Each service's `declared` lists every external's declarations; reading it, not `s.externals`, checks the list the
  -- step encodes requests from.
  let unknownHandles := handles.filterMap fun h => match h.name with
    | none => some (Illegal.handleName, s!"one {h.kind} handle's name is no string literal; write it as one, so check can see which request it names")
    | some n =>
      if !h.kind.startsWith "external" || s.services.all fun v =>
        v.declared.any fun (_, d) => d.kind == h.kind && d.name == n && (Ty.sames d.types h.types).isSome then none
      else some (Illegal.unknownHandle, s!"no external declares the {h.kind} {n} with these types; add it to an external's declares")
  let capturedKeys := captures.filterMap fun (site, Γ) => if (Ty.tuple Γ).plainKeys then none else
    some (Illegal.tableKey, s!"{site.module}:{site.line}:{site.col}: a function a structure value keeps captures a table whose key is no plain value; {tableKeyAdvice}")
  topNames ++ sharedOwners ++ perService ++ perExternal ++ unknownHandles ++ capturedKeys

end Tazuna.Ir
