import Tazuna.Ir.Time
import Tazuna.Ir.Expr
import Tazuna.Semantics.Service.Functions
import Tazuna.Semantics.Service.Note
import Tazuna.Semantics.Instrument.Collect

/-!
The evaluator of IR expressions. Values stay as JSON encodes them: the converter has chosen each operation by the TS type
of its operands (an instant compare, a Bag's `every`), so no value needs decoding. A record is a handle that reads a
field only when an expression reads it, so an evaluation reads the parts of the records that TS's records view reads.
-/

namespace Tazuna.Semantics.Eval

open Tazuna.Ir Tazuna.Semantics.Service Tazuna.Semantics.Instrument

/-- A value of a chart function's arguments that notes each field that an expression reads, as TS's arguments do. -/
inductive Tracked where
  /-- The context; a field of `copied` is the copy's. -/
  | context (copied : List String)
  | shown
  /-- Whether each state is active; a state of `copied` is the copy's. -/
  | active (copied : List String)
  /-- The parameters of `state`: reading one reads the state's visit, and reading a name it lacks is unheld. -/
  | held (holder : Holder) (state : Option String)
deriving Inhabited

/-- A value as an expression sees it. -/
inductive Val where
  | undef
  | json (value : Value)
  /--
  The record of `key` of `entity` in `source`, none for a single entity's. A record and a table read the records that
  made them, as TS's records view does: a binds value read in an ensures holds the records from before the write.
  -/
  | row (source : Records) (entity : String) (key : Option Value)
  /-- The records of a keyed entity in `source`. -/
  | table (source : Records) (entity : String)
  /-- A Bag or array that an operation made. -/
  | list (values : List Val)
  | obj (fields : List (String × Val))
  | tracked (tracked : Tracked) (value : Value)
  | emit (event : Ir.Ref) (payload : Val)
deriving Inhabited

def Val.ofOption : Option Value → Val
  | some v => .json v
  | none => .undef

/-- What an expression reads besides its variables, and the field names of each entity, in its schema's order. -/
structure Env where
  args : Arg → Val := fun _ => .undef
  records : Records := []
  fields : String → List String := fun _ => []
  /-- The key fields of each keyed entity. -/
  keyFields : String → List String := fun _ => []
  /-- What createKey returns next. -/
  keys : Keys := {}
  /-- Whether the records are another service's, which a read stops at (`Trace.readHidden`). -/
  hidden : Bool := false

/--
What an evaluation read and made: the parts of the records, in order and once, the chart values, in order, and the
keys it created.
-/
structure Trace where
  parts : List RecordPart := []
  access : Access := {}
  /-- The entities that createKey made a key of, in call order. -/
  created : List String := []
  /-- Whether the evaluation stopped at reading records that `Env.hidden` hides. -/
  readHidden : Bool := false

/-- An evaluation, which notes what it reads, also when an Issue stops it. -/
abbrev EvalM := ExceptT Issue (StateM Trace)

def note (part : RecordPart) : EvalM Unit :=
  modify fun t => if part ∈ t.parts then t else { t with parts := t.parts ++ [part] }

def touch (f : Access → Access) : EvalM Unit := modify fun t => { t with access := f t.access }

/-- The value of `x` and what it read. -/
def EvalM.run' {α : Type} (x : EvalM α) : Except Issue α × Trace := (ExceptT.run x).run {}

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

/-- The number or days that `order` reads of a value to compare it, as a numerator over 10 ^ the exponent. -/
def ordinal (order : Order) : Val → Option (Int × Nat)
  | .json (.num n) => if order == .number then some (n.mantissa, n.exponent) else none
  | .json (.str s) => if order == .date then (parseDate? s).map (·, 0) else none
  | _ => none

def Relation.holds {α : Type} [LT α] [LE α] [BEq α] [DecidableRel (α := α) (· < ·)] [DecidableRel (α := α) (· ≤ ·)]
    (r : Relation) (a b : α) : Bool :=
  match r with
  | .lt => a < b
  | .le => a ≤ b
  | .gt => a > b
  | .ge => a ≥ b
  | .eq => a == b

def thrown {α : Type} : EvalM α := throw (.thrown none)

/-- The object that `v` is, as the key of an entity with several key fields: a JSON object, or an object of JSON values
that an expression built; none for anything else. -/
def keyObject? : Val → Option Value
  | .json (.obj fields) => some (.obj fields)
  | .obj fields => (fields.mapM fun ((n, v) : String × Val) => match v with | .json x => some (n, x) | _ => none).map .obj
  | _ => none

/-- The stop at reading hidden records, as TS's unreadable records throw on the first property read. -/
def readHidden {α : Type} : EvalM α := do
  modify fun t => { t with readHidden := true }
  thrown

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
  | .tracked tracked v =>
    match v.field? name, tracked with
    | none, .held .. => throw (.unheld name)
    | none, _ => pure .undef
    | some x, .context copied => do
      touch fun a => { a with context := a.context ++ [(if name ∈ copied then .copy else .owner, name)] }
      pure (.json x)
    | some x, .shown => do
      touch fun a => { a with shown := a.shown ++ [name] }
      pure (.json x)
    | some x, .active copied => do
      touch fun a => { a with active := a.active ++ [(if name ∈ copied then .copy else .owner, name)] }
      pure (.json x)
    | some x, .held holder state => do
      if let some s := state then touch fun a => { a with active := a.active ++ [(holder, s)] }
      pure (.json x)
  | _ => pure .undef

/--
The keys of the records of `entity`, in the order that the records hold them. A Bag has no order, and no operation
exposes the order in which it visits one (`Functions.comparable` ignores it), so a table visits its records as they
are held: prove's slots hold them in the same order.
-/
def heldKeys (records : Records) (entity : String) : List Value :=
  (records.filter (·.entity == entity)).filterMap (·.key)

/-- The values that a callback method visits. Visiting a table reads its keys and visits its records as they are held. -/
def elements : Val → EvalM (List Val)
  | .json (.arr vs) => pure (vs.map .json)
  | .list vs => pure vs
  | .table source entity => do
    note (.keys entity)
    pure ((heldKeys source entity).map fun k => .row source entity (some k))
  | _ => thrown

/-- A key as a numerator over 10 ^ the exponent, which `order` reads of a value, or the TypeError that JS would throw. -/
def keyOf (order : Order) (v : Val) : EvalM (Int × Nat) :=
  match ordinal order v with
  | some k => pure k
  | none => thrown

def keyLt (a b : Int × Nat) : Bool := a.1 * 10 ^ b.2 < b.1 * 10 ^ a.2

/-- The integer that a number is, when it is a safe integer, as `Number.isSafeInteger` takes it. -/
def safeInteger? : Val → Option Int
  | .json (.num n) =>
    let d : Int := 10 ^ n.exponent
    if n.mantissa % d == 0 && (n.mantissa / d).natAbs < 2 ^ 53 then some (n.mantissa / d) else none
  | _ => none

/-- The least key of `keyed` under `lt`, the first of equal ones, as a Bag's min reduces the keys in visit order. -/
def least (lt : Int × Nat → Int × Nat → Bool) : List (Val × (Int × Nat)) → Val
  | [] => .undef
  | k :: ks => (ks.foldl (fun m k => if lt k.2 m.2 then k else m) k).1

/-- Groups of equal key in ascending key order, each in the order of `keyed`, as TS's runsOf makes them. -/
def runs (keyed : List (Val × (Int × Nat))) : List (List Val) :=
  let sorted := keyed.mergeSort fun a b => !keyLt b.2 a.2
  let groups := sorted.foldl (fun (acc : List (List (Val × (Int × Nat)))) k =>
    match acc with
    | (g :: gs) => match g.head? with
      | some h => if !keyLt h.2 k.2 && !keyLt k.2 h.2 then (g ++ [k]) :: gs else [k] :: g :: gs
      | none => [k] :: gs
    | [] => [[k]]) []
  groups.reverse.map (·.map (·.1))

def Arith.apply : Arith → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- The integer that a number is. -/
def integer? : Val → Option Int
  | .json (.num n) =>
    let d : Int := 10 ^ n.exponent
    if n.mantissa % d == 0 then some (n.mantissa / d) else none
  | _ => none

mutual

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
    let right ← eval env vars b
    match ordinal order left, ordinal order right with
    | some (m, e), some (m', e') => pure (.json (.bool (Relation.holds r (m * 10 ^ e') (m' * 10 ^ e))))
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
    let tested ← (← elements (← eval env vars c)).mapM fun v => do pure (v, truthy (← eval env ((x, v) :: vars) body))
    pure (.list (tested.filterMap fun (v, kept) => if kept then some v else none))
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
  | .table entity => do
    if env.hidden then readHidden
    pure (.table env.records entity)
  | .single entity => do
    if env.hidden then readHidden
    pure (.row env.records entity none)
  | .lookup t k => do
    let table ← eval env vars t
    match table, ← eval env vars k with
    | .table source entity, .json (.str key) => do
      note (.record entity (.str key))
      pure (if source.any (fun r => r.entity == entity && r.key == some (.str key)) then .row source entity (some (.str key))
        else .undef)
    | .table source entity, k@(.json (.obj _)) | .table source entity, k@(.obj _) => do
      -- The key of an entity with several key fields, an object.
      let some k := keyObject? k | thrown
      let key := canonicalKey (env.keyFields entity) k
      note (.record entity key)
      pure (if source.any (fun r => r.entity == entity && r.key == some key) then .row source entity (some key) else .undef)
    | _, _ => thrown
  | .obj fields => do pure (.obj (← evalFields env vars fields))
  | .arr values => do pure (.list (← evalAll env vars values))
  | .map _ c x body => do
    let vs ← elements (← eval env vars c)
    pure (.list (← vs.mapM fun v => eval env ((x, v) :: vars) body))
  | .sum c x body => do
    let ns ← (← elements (← eval env vars c)).mapM fun v => eval env ((x, v) :: vars) body
    let some (ints : List Int) := ns.mapM safeInteger? | thrown
    let total : Int := ints.foldl (· + ·) 0
    if total.natAbs < 2 ^ 53 then pure (.json (.num total)) else thrown
  | .min order c x body => do
    let keyed ← (← elements (← eval env vars c)).mapM fun v => do
      let k ← eval env ((x, v) :: vars) body
      pure (k, ← keyOf order k)
    pure (least keyLt keyed)
  | .max order c x body => do
    let keyed ← (← elements (← eval env vars c)).mapM fun v => do
      let k ← eval env ((x, v) :: vars) body
      pure (k, ← keyOf order k)
    pure (least (fun a b => keyLt b a) keyed)
  | .only c => do
    match ← elements (← eval env vars c) with
    | [] => pure .undef
    | [v] => pure v
    | _ => throw .notOnly
  | .sortedBy order c x body => do
    let keyed ← (← elements (← eval env vars c)).mapM fun v => do
      pure (v, ← keyOf order (← eval env ((x, v) :: vars) body))
    pure (.list ((runs keyed).map .list))
  | .concat a b => do
    let left ← eval env vars a
    let right ← eval env vars b
    let vs ← elements left
    pure (.list (vs ++ (← elements right)))
  | .emit event payload => do pure (.emit event (← eval env vars payload))
  | .includes a v => do
    let vs ← elements (← eval env vars a)
    let value ← eval env vars v
    pure (.json (.bool (vs.any (same · value))))
  | .arith operation a b => do
    let left ← eval env vars a
    match integer? left, integer? (← eval env vars b) with
    | some x, some y => pure (.json (.num (Arith.apply operation x y)))
    | _, _ => thrown
  | .addDays d n => do
    let date ← eval env vars d
    match ordinal .date date, integer? (← eval env vars n) with
    | some (days, _), some more =>
      match renderDate? (days + more) with
      | some label => pure (.json (.str label))
      | none => thrown
    | _, _ => thrown
  | .createKey entity => do
    modify fun t => { t with created := t.created ++ [entity] }
    match (givenKeys env.keys (← get).created).getLast? with
    | some (_, key) => pure (.json (.str key))
    | none => thrown

def evalAll (env : Env) (vars : List (String × Val)) : List Expr → EvalM (List Val)
  | [] => pure []
  | e :: es => do
    let v ← eval env vars e
    pure (v :: (← evalAll env vars es))

def evalFields (env : Env) (vars : List (String × Val)) : List Field → EvalM (List (String × Val))
  | [] => pure []
  | ⟨name, e⟩ :: fs => do
    let v ← eval env vars e
    pure ((name, v) :: (← evalFields env vars fs))

end

/--
The JSON of a value, none for `undefined`, as TS's encoding and JSON.stringify write it. A record reads every field of
its entity, in the schema's order, as encoding the records view's record does, and a table is the list of its records.
-/
partial def encode (env : Env) : Val → EvalM (Option Value)
  | .undef => pure none
  | .json v => pure (some v)
  | .list vs => do pure (some (.arr (← vs.mapM fun v => do pure ((← encode env v).getD .null))))
  | .obj fields => do
    pure (some (.obj (← fields.filterMapM fun (name, v) => do pure ((← encode env v).map (name, ·)))))
  | .row source entity key => do
    let present ← (env.fields entity).filterMapM fun name => do
      match ← fieldOf (.row source entity key) name with
      | .json v => pure (some (name, v))
      | _ => pure none
    pure (some (.obj present))
  | .table source entity => do encode env (.list (← elements (.table source entity)))
  | .tracked _ v => pure (some v)
  | .emit _ payload => do pure (some (.obj [("kind", .str "emit"), ("payload", (← encode env payload).getD .null)]))

/-- The JSON that TS's encoding of a spec function's value gives: null for `undefined`, as JSON.stringify writes it. -/
def answerOf (env : Env) (v : Val) : EvalM Value := do pure ((← encode env v).getD .null)

/-- The name of the first of `conditions` whose value is not truthy, in order, as TS `firstFailing` finds it. -/
def firstFailing (env : Env) : List Condition → EvalM (Option String)
  | [] => pure none
  | c :: cs => do if truthy (← eval env [] c.body) then firstFailing env cs else pure (some c.name)

/-- The binds values of `binds`, in order, as an object, as TS computes `bound` before a condition reads it. -/
def bound (env : Env) (binds : List Condition) : EvalM Val := do
  pure (.obj (← binds.mapM fun b => do pure (b.name, ← eval env [] b.body)))

end Tazuna.Semantics.Eval
