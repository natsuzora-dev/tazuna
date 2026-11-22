import Tazuna.Data.Time
import Tazuna.Ir.Expr
import Tazuna.Service.Functions
import Tazuna.Service.Note

/-!
The evaluator of IR expressions. Values stay as JSON encodes them: the converter has chosen each operation by the TS type
of its operands (an instant compare, a Bag's `every`), so no value needs decoding. A record is a handle that reads a
field only when an expression reads it, so an evaluation reads the parts of the records that TS's records view reads.
-/

namespace Tazuna.Ir

open Tazuna.Data Tazuna.Service

/-- A value as an expression sees it. -/
inductive Val where
  | undef
  | json (value : Value)
  /--
  The record of `key` of `entity` in `source`, none for a single entity's. A record and a table read the records that
  made them, as TS's records view does: a binds value read in an ensures holds the records from before the write.
  -/
  | row (source : Records) (entity : String) (key : Option String)
  /-- The records of a keyed entity in `source`. -/
  | table (source : Records) (entity : String)
  /-- A Bag or array that an operation made. -/
  | list (values : List Val)
  | obj (fields : List (String × Val))
deriving Inhabited

def Val.ofOption : Option Value → Val
  | some v => .json v
  | none => .undef

/-- What an expression reads besides its variables. -/
structure Env where
  args : Arg → Val := fun _ => .undef
  records : Records := []

/-- An evaluation, which notes each part of the records that it reads, in order and once, also when an Issue stops it. -/
abbrev EvalM := ExceptT Issue (StateM (List RecordPart))

def note (part : RecordPart) : EvalM Unit :=
  modify fun parts => if part ∈ parts then parts else parts ++ [part]

/-- The value of `x` and the parts of the records that it read. -/
def EvalM.run' {α : Type} (x : EvalM α) : Except Issue α × List RecordPart := (ExceptT.run x).run []

/-- Whether JS takes the value as true: all but `undefined`, null, false, 0 and the empty string. -/
def truthy : Val → Bool
  | .undef | .json .null => false
  | .json (.bool b) => b
  | .json (.num n) => n.mantissa != 0
  | .json (.str s) => !s.isEmpty
  | _ => true

/-- JS `===` on scalars, null and undefined. Two arrays, objects or records are never the same value. -/
def same : Val → Val → Bool
  | .undef, .undef => true
  | .json .null, .json .null => true
  | .json (.bool a), .json (.bool b) => a == b
  | .json (.num a), .json (.num b) => a.mantissa * 10 ^ b.exponent == b.mantissa * 10 ^ a.exponent
  | .json (.str a), .json (.str b) => a == b
  | _, _ => false

/-- The number, ms or days that `order` reads of a value to compare it, as a numerator over 10 ^ the exponent. -/
def ordinal (order : Order) : Val → Option (Int × Nat)
  | .json (.num n) => if order == .number then some (n.mantissa, n.exponent) else none
  | .json (.str s) =>
    match order with
    | .instant => (parseTime s).toOption.map (·, 0)
    | .date => (parseDate s).toOption.map (·, 0)
    | .number => none
  | _ => none

def Relation.holds (r : Relation) (a b : Int) : Bool :=
  match r with
  | .lt => a < b
  | .le => a ≤ b
  | .gt => a > b
  | .ge => a ≥ b
  | .eq => a == b

def thrown {α : Type} : EvalM α := throw (.thrown none)

/-- A string operation's operands, or the TypeError of reading a property of null or undefined. -/
def strings (string search : Val) : EvalM (String × String) :=
  match string, search with
  | .json (.str s), .json (.str p) => pure (s, p)
  | _, _ => thrown

def isInfix (p s : List Char) : Bool := (List.range (s.length + 1)).any fun i => p.isPrefixOf (s.drop i)

/-- The field `name` of a value that is neither null nor undefined. Reading a record's field reads that field. -/
def fieldOf (v : Val) (name : String) : EvalM Val :=
  match v with
  | .json v => pure (.ofOption (v.field? name))
  | .row source entity key => do
    note (.field entity key name)
    let row := source.find? fun r => r.entity == entity && r.key == key
    pure (.ofOption (row.bind (·.value.field? name)))
  | .obj fields => pure ((fields.lookup name).getD .undef)
  | _ => pure .undef

/-- The values that a callback method visits. Visiting a table reads its keys and visits its records in key order. -/
def elements : Val → EvalM (List Val)
  | .json (.arr vs) => pure (vs.map .json)
  | .list vs => pure vs
  | .table source entity => do
    note (.keys entity)
    pure ((source.keys entity).map fun k => .row source entity (some k))
  | _ => thrown

/--
The value of `e` in `env` with the variables `vars`. A property of null or undefined is the TypeError `thrown none`, as
JS throws it; so is a variable that no binder declares, which the converter never writes.
-/
def eval (env : Env) (vars : List (String × Val)) : Expr → EvalM Val
  | .undef => pure .undef
  | .lit v => pure (.json v)
  | .arg a => pure (env.args a)
  | .var x => match vars.lookup x with
    | some v => pure v
    | none => thrown
  | .let x e body => do eval env ((x, ← eval env vars e) :: vars) body
  | .ite c yes no => do if truthy (← eval env vars c) then eval env vars yes else eval env vars no
  | .and a b => do
    let v ← eval env vars a
    if truthy v then eval env vars b else pure v
  | .or a b => do
    let v ← eval env vars a
    if truthy v then pure v else eval env vars b
  | .coalesce a b => do
    match ← eval env vars a with
    | .undef | .json .null => eval env vars b
    | v => pure v
  | .not a => do pure (.json (.bool !truthy (← eval env vars a)))
  | .eq a b => do
    let left ← eval env vars a
    pure (.json (.bool (same left (← eval env vars b))))
  | .compare r order a b => do
    let left ← eval env vars a
    match ordinal order left, ordinal order (← eval env vars b) with
    | some (m, e), some (m', e') => pure (.json (.bool (r.holds (m * 10 ^ e') (m' * 10 ^ e))))
    | _, _ => thrown
  | .field o name => do
    match ← eval env vars o with
    | .undef | .json .null => thrown
    | v => fieldOf v name
  | .fieldOpt o name => do
    match ← eval env vars o with
    | .undef | .json .null => pure .undef
    | v => fieldOf v name
  | .strLen s => do
    match ← eval env vars s with
    | .json (.str s) => pure (.json (.num s.length))
    | _ => thrown
  | .startsWith s p => do
    let string ← eval env vars s
    let (s, p) ← strings string (← eval env vars p)
    pure (.json (.bool (p.toList.isPrefixOf s.toList)))
  | .endsWith s p => do
    let string ← eval env vars s
    let (s, p) ← strings string (← eval env vars p)
    pure (.json (.bool (p.toList.reverse.isPrefixOf s.toList.reverse)))
  | .strIncludes s p => do
    let string ← eval env vars s
    let (s, p) ← strings string (← eval env vars p)
    pure (.json (.bool (isInfix p.toList s.toList)))
  | .size c => do
    match ← eval env vars c with
    | .json (.arr vs) => pure (.json (.num vs.length))
    | .list vs => pure (.json (.num vs.length))
    | .table source entity => do
      note (.keys entity)
      pure (.json (.num (source.keys entity).length))
    | _ => thrown
  | .filter _ c x body => do
    let vs ← elements (← eval env vars c)
    pure (.list (← vs.filterM fun v => do pure (truthy (← eval env ((x, v) :: vars) body))))
  | .some .array c x body => do
    let vs ← elements (← eval env vars c)
    pure (.json (.bool (← vs.anyM fun v => do pure (truthy (← eval env ((x, v) :: vars) body)))))
  | .some .bag c x body => do
    let results ← (← elements (← eval env vars c)).mapM fun v => eval env ((x, v) :: vars) body
    pure (.json (.bool (results.any (same · (.json (.bool true))))))
  | .every .array c x body => do
    let vs ← elements (← eval env vars c)
    pure (.json (.bool (← vs.allM fun v => do pure (truthy (← eval env ((x, v) :: vars) body)))))
  | .every .bag c x body => do
    let results ← (← elements (← eval env vars c)).mapM fun v => eval env ((x, v) :: vars) body
    pure (.json (.bool !(results.any (same · (.json (.bool false))))))
  | .table entity => pure (.table env.records entity)
  | .single entity => pure (.row env.records entity none)
  | .lookup t k => do
    let table ← eval env vars t
    match table, ← eval env vars k with
    | .table source entity, .json (.str key) => do
      note (.record entity key)
      pure (if source.any (fun r => r.entity == entity && r.key == some key) then .row source entity (some key) else .undef)
    | _, _ => thrown

/-- The JSON of a value, none for `undefined`, as JSON.stringify writes it; a record or table has none. -/
partial def Val.encoded : Val → Except Issue (Option Value)
  | .undef => pure none
  | .json v => pure (some v)
  | .list vs => do pure (some (.arr (← vs.mapM fun v => do pure ((← v.encoded).getD .null))))
  | .obj fields => do
    pure (some (.obj (← fields.filterMapM fun (name, v) => do pure ((← v.encoded).map (name, ·)))))
  | .row .. | .table .. => throw (.thrown none)

/-- The name of the first of `conditions` whose value is not truthy, in order, as TS `firstFailing` finds it. -/
def firstFailing (env : Env) : List Condition → EvalM (Option String)
  | [] => pure none
  | c :: cs => do if truthy (← eval env [] c.body) then firstFailing env cs else pure (some c.name)

/-- The binds values of `binds`, in order, as an object, as TS computes `bound` before a condition reads it. -/
def bound (env : Env) (binds : List Condition) : EvalM Val := do
  pure (.obj (← binds.mapM fun b => do pure (b.name, ← eval env [] b.body)))

end Tazuna.Ir
