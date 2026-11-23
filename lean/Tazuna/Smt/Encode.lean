import Tazuna.Smt.Date
import Tazuna.Ir.Eval

/-!
The encoding of IR expressions as terms over symbolic records: `seval` mirrors Ir.eval, case for case, on symbolic
values, and gives each expression's value and the term that holds when its evaluation throws. Thm.Smt.Encode proves
that the encoding agrees with Ir.eval under every model (`seval_agrees`). An expression outside the encoded operations
is no encoding, with the reason.
-/

namespace Tazuna.Smt

open Tazuna.Data Tazuna.Ir Tazuna.Service

/-- The JSON of a scalar, none for `undefined`. An integer is the JSON number with exponent 0. -/
def Scalar.toValue? : Scalar → Option Value
  | .undef => none
  | .null => some .null
  | .bool b => some (.bool b)
  | .int n => some (.num ⟨n, 0⟩)
  | .str s => some (.str s)

def Scalar.toVal (v : Scalar) : Val := Val.ofOption v.toValue?

/-- A record slot of a keyed entity: whether a record is in it, its key, and its fields, each a `V`. -/
structure Slot where
  live : Term
  key : Term
  fields : List (String × Term)
deriving Repr, Inhabited

/-- Symbolic records: the slots of each keyed entity, in record order, and the fields of each single entity's record. -/
structure SRecords where
  keyed : List (String × List Slot) := []
  singles : List (String × List (String × Term)) := []
deriving Repr, Inhabited

/-- The fields that are not `undefined` under `M`, as a JSON object holds them. -/
def present (M : Model) (fields : List (String × Term)) : List (String × Value) :=
  fields.filterMap fun (n, t) => ((t.denote M).toScalar.toValue?).map (n, ·)

def Slot.row (M : Model) (entity : String) (s : Slot) : Row :=
  { entity, key := some (s.key.denote M).toStr, value := .obj (present M s.fields) }

/-- The records that `r` holds under `M`: the live slots of each keyed entity, then the single entities' records. -/
def SRecords.conc (M : Model) (r : SRecords) : Records :=
  (r.keyed.flatMap fun (e, slots) => (slots.filter (·.live.holds M)).map (Slot.row M e)) ++
    r.singles.map fun (e, fields) => { entity := e, key := none, value := .obj (present M fields) }

/-- The slots of `entity`, in record order. -/
def SRecords.slotsOf (r : SRecords) (entity : String) : List Slot :=
  (r.keyed.filter (·.1 == entity)).flatMap (·.2)

/-- A symbolic value: the shape that an evaluation gives, with terms where the value depends on the model. -/
inductive SVal where
  /-- A JSON scalar or `undefined`. -/
  | scalar (t : Term)
  /-- A JSON object that an argument holds, such as an input: the fields that are not `undefined`. -/
  | json (fields : List (String × Term))
  /-- The record of `entity` with the key `key`, a String term. -/
  | row (entity : String) (key : Term)
  | single (entity : String)
  | table (entity : String)
  | obj (fields : List (String × SVal))
  | list (values : List SVal)
  /--
  A collection that an operation on a Bag made: each value with the term that holds when the value is in it, in the
  order that the operation visits them.
  -/
  | bag (items : List (Term × SVal))
  | emit (event : Spec.Ref) (payload : SVal)
  | ite (c : Term) (a b : SVal)
deriving Repr, Inhabited

mutual

/-- The value that `v` is under `M`, with `records` the records that the evaluation reads. -/
def SVal.conc (M : Model) (records : Records) : SVal → Val
  | .scalar t => (t.denote M).toScalar.toVal
  | .json fields => .json (.obj (present M fields))
  | .row e k => .row records e (some (k.denote M).toStr)
  | .single e => .row records e none
  | .table e => .table records e
  | .obj fields => .obj (SVal.concFields M records fields)
  | .list vs => .list (SVal.concAll M records vs)
  | .bag items => .list (SVal.concItems M records items)
  | .emit event payload => .emit event (payload.conc M records)
  | .ite c a b => if c.holds M then a.conc M records else b.conc M records

def SVal.concAll (M : Model) (records : Records) : List SVal → List Val
  | [] => []
  | v :: vs => v.conc M records :: SVal.concAll M records vs

def SVal.concFields (M : Model) (records : Records) : List (String × SVal) → List (String × Val)
  | [] => []
  | (n, v) :: fs => (n, v.conc M records) :: SVal.concFields M records fs

/-- The values of the items whose terms hold under `M`, in order. -/
def SVal.concItems (M : Model) (records : Records) : List (Term × SVal) → List Val
  | [] => []
  | (g, v) :: items => if g.holds M then v.conc M records :: SVal.concItems M records items
    else SVal.concItems M records items

end

def mkBoolT (t : Term) : Term := .mkBool t
def intLit (n : Int) : Term := .lit (.int n)
def strLit (s : String) : Term := .lit (.str s)

/-- Whether JS takes the scalar as true. -/
def truthyT (t : Term) : Term :=
  .or (.and (.isBool t) (.boolOf t))
    (.or (.and (.isInt t) (.not (.eq (.intOf t) (intLit 0)))) (.and (.isStr t) (.not (.eq (.strOf t) (strLit "")))))

def nullishT (t : Term) : Term := .or (.isUndef t) (.isNull t)

/-- JS `===` on two scalars. -/
def sameT (a b : Term) : Term :=
  .or (.and (.isUndef a) (.isUndef b))
    (.or (.and (.isNull a) (.isNull b))
      (.or (.and (.and (.isBool a) (.isBool b)) (.eq (.boolOf a) (.boolOf b)))
        (.or (.and (.and (.isInt a) (.isInt b)) (.eq (.intOf a) (.intOf b)))
          (.and (.and (.isStr a) (.isStr b)) (.eq (.strOf a) (.strOf b))))))

def SVal.truthy : SVal → Term
  | .scalar t => truthyT t
  | .ite c a b => .ite c a.truthy b.truthy
  | _ => tt

def SVal.nullish : SVal → Term
  | .scalar t => nullishT t
  | .ite c a b => .ite c a.nullish b.nullish
  | _ => ff

def SVal.same : SVal → SVal → Term
  | .ite c a b, w => .ite c (a.same w) (b.same w)
  | .scalar a, .ite c x y => .ite c (SVal.same (.scalar a) x) (SVal.same (.scalar a) y)
  | .scalar a, .scalar b => sameT a b
  | _, _ => ff

/-- The scalar that `v` is, and the term that holds when `v` is no scalar. -/
def SVal.scalarOf : SVal → Term × Term
  | .scalar t => (t, ff)
  | .ite c a b => (.ite c a.scalarOf.1 b.scalarOf.1, .ite c a.scalarOf.2 b.scalarOf.2)
  | _ => (undefT, tt)

/-- The field `name` of a JSON object's fields: the first that is not `undefined`, as JSON drops the others. -/
def jsonField (name : String) : List (String × Term) → Term
  | [] => undefT
  | (n, t) :: fs => if n == name then .ite (.isUndef t) (jsonField name fs) t else jsonField name fs

/-- Whether the key of a live slot of `slots` is `key`. -/
def keyIn (key : Term) (slots : List Slot) : Term :=
  disj (slots.map fun s => .and s.live (.eq (.mkStr s.key) (.mkStr key)))

/-- The field `name` of the first live slot of `slots` whose key is `key`, `undefined` when none is. -/
def rowField (key : Term) (name : String) : List Slot → Term
  | [] => undefT
  | s :: ss => .ite (.and s.live (.eq (.mkStr s.key) (.mkStr key))) (jsonField name s.fields) (rowField key name ss)

/-- The number of items whose terms hold. -/
def countIn : List (Term × SVal) → Term
  | [] => intLit 0
  | (g, _) :: items => .add (.ite g (intLit 1) (intLit 0)) (countIn items)

/-- The number of live slots. -/
def liveCount : List Slot → Term
  | [] => intLit 0
  | s :: ss => .add (.ite s.live (intLit 1) (intLit 0)) (liveCount ss)

/-- The field `name` of a value that is neither null nor `undefined`. -/
def SVal.field (r : SRecords) (name : String) : SVal → SVal
  | .json fields => .scalar (jsonField name fields)
  | .row e k => .scalar (rowField k name (r.slotsOf e))
  | .single e => .scalar (match r.singles.lookup e with
    | some fields => jsonField name fields
    | none => undefT)
  | .obj fields => (fields.lookup name).getD (.scalar undefT)
  | .ite c a b => .ite c (a.field r name) (b.field r name)
  | _ => .scalar undefT

/-- `table.get(key)` and the term that holds when it throws. -/
def SVal.lookup (r : SRecords) (key : SVal) : SVal → SVal × Term
  | .table e =>
    let (k, notScalar) := key.scalarOf
    (.ite (keyIn (.strOf k) (r.slotsOf e)) (.row e (.strOf k)) (.scalar undefT), .or notScalar (.not (.isStr k)))
  | .ite c a b =>
    let (x, xe) := SVal.lookup r key a
    let (y, ye) := SVal.lookup r key b
    (.ite c x y, .ite c xe ye)
  | _ => (.scalar undefT, tt)

/-- The size of a collection and the term that holds when `v` is none. -/
def SVal.size (r : SRecords) : SVal → SVal × Term
  | .table e => (.scalar (.mkInt (liveCount (r.slotsOf e))), ff)
  | .list vs => (.scalar (.mkInt (intLit vs.length)), ff)
  | .bag items => (.scalar (.mkInt (countIn items)), ff)
  | .ite c a b => (.ite c (a.size r).1 (b.size r).1, .ite c (a.size r).2 (b.size r).2)
  | _ => (.scalar undefT, tt)

/-- `array.includes(value)` and the term that holds when it throws. A table's records are never `===` to a value. -/
def SVal.includes (value : SVal) : SVal → Term × Term
  | .list vs => (disj (vs.map (·.same value)), ff)
  | .bag items => (disj (items.map fun (g, v) => .and g (v.same value)), ff)
  | .table _ => (ff, ff)
  | .ite c a b =>
    (.ite c (SVal.includes value a).1 (SVal.includes value b).1, .ite c (SVal.includes value a).2 (SVal.includes value b).2)
  | _ => (ff, tt)

/--
The values that an operation visits in a collection, each with the term that holds when it is there, in visit order: a
table's records in slot order, which is the order that `SRecords.conc` holds them in. None for what may be no collection.
-/
def SVal.items (r : SRecords) : SVal → Option (List (Term × SVal))
  | .list vs => some (vs.map (tt, ·))
  | .bag items => some items
  | .table e => some ((r.slotsOf e).map fun s => (s.live, .row e s.key))
  | .ite c a b => do
    let xs ← a.items r
    let ys ← b.items r
    pure (xs.map (fun (g, v) => (.and c g, v)) ++ ys.map fun (g, v) => (.and (.not c) g, v))
  | _ => none

/-- An item of a callback method: the term that holds when the value is visited, the value, and the callback's result. -/
abbrev Visit := Term × SVal × (SVal × Term)

/-- The term that holds when the callback throws on a visited value. -/
def thrownIn (visits : List Visit) : Term := disj (visits.map fun q => .and q.1 q.2.2.2)

/-- A safe integer bound: `Number.isSafeInteger` takes integers whose magnitude is below `2 ^ 53`. -/
def safeT (t : Term) : Term := .and (.lt (intLit (-(2 ^ 53))) t) (.lt t (intLit (2 ^ 53)))

/-- The sum of the integers that the visited values give, and the term that holds when one is no safe integer. -/
def sumIn : List Visit → Term × Term
  | [] => (intLit 0, ff)
  | (g, _, (b, _)) :: visits =>
    let (x, bad) := b.scalarOf
    let (total, rest) := sumIn visits
    (.add (.ite g (.intOf x) (intLit 0)) total, .or (.and g (.or bad (.not (.and (.isInt x) (safeT (.intOf x)))))) rest)

/--
The least key of the visited values under `lt`, the first of equal ones, as `least` finds it: `found` holds once a value
was visited, and `m` is the key so far, `undefined` before.
-/
def leastIn (lt : Term → Term → Term) : Term → Term → List Visit → Term
  | _, m, [] => m
  | found, m, (g, _, (b, _)) :: visits =>
    let k := b.scalarOf.1
    leastIn lt (.or found g) (.ite (.and g (.or (.not found) (lt k m))) k m) visits

/-- The term that holds when a key of a visited value is no integer, which an integer min or max throws on. -/
def keysBad (visits : List Visit) : Term :=
  disj (visits.map fun q => .and q.1 (.or q.2.2.1.scalarOf.2 (.not (.isInt q.2.2.1.scalarOf.1))))

/-- The first item whose term holds, `undefined` when none does. -/
def firstIn : List (Term × SVal) → SVal
  | [] => .scalar undefT
  | (g, v) :: items => .ite g v (firstIn items)

/-- The term that holds when the terms of two items hold. -/
def twoIn : List (Term × SVal) → Term
  | [] => ff
  | (g, _) :: items => .or (.and g (disj (items.map (·.1)))) (twoIn items)

def trueT : SVal := .scalar (.lit (.val (.bool true)))
def falseT : SVal := .scalar (.lit (.val (.bool false)))

/-- That the scalar `t` is a date label. -/
def dateT (t : Term) : Term := .and (.isStr t) (dateValidT (.strOf t))

/--
That the scalar `t` is a date label (`dateT`), read off the day number where `t` is the label of one that the encoding
made: a day variable, or a sum such as addDays makes.
-/
def isDateOf : Term → Term
  | .mkStr (.dateLabel (.var x .int)) => inRangeT (.var x .int)
  | .mkStr (.dateLabel (.add a b)) => inRangeT (.add a b)
  | .ite c a b => .ite c (isDateOf a) (isDateOf b)
  | t => dateT t

/-- The day number of the date label `t`, read off as `isDateOf` reads it, else parsed. -/
def dayOf : Term → Term
  | .mkStr (.dateLabel (.var x .int)) => .var x .int
  | .mkStr (.dateLabel (.add a b)) => .add a b
  | .ite c a b => .ite c (dayOf a) (dayOf b)
  | t => dayT (.strOf t)

def relT (r : Relation) (a b : Term) : Term :=
  match r with
  | .lt => .lt a b
  | .le => .le a b
  | .gt => .lt b a
  | .ge => .le b a
  | .eq => .eq a b

def arithT (op : Arith) (a b : Term) : Term :=
  match op with
  | .add => .add a b
  | .sub => .sub a b
  | .mul => .mul a b

/-- A literal as a scalar term: null, a boolean, an integer, or a string that SMT strings hold. -/
def litTerm : Value → Except String Term
  | .null => pure (.lit (.val .null))
  | .bool b => pure (.lit (.val (.bool b)))
  | .num n => if n.exponent == 0 then pure (.lit (.val (.int n.mantissa))) else throw "a decimal literal"
  | .str s =>
    if s.toList.all (·.toNat ≤ 0x2FFFF) then pure (.lit (.val (.str s)))
    else throw "a string literal with a character above U+2FFFF, which SMT strings lack"
  | _ => throw "an array or object literal"

/-- What an expression reads: its arguments, as symbolic values, and the records. -/
structure SEnv where
  args : Arg → Option SVal := fun _ => none
  records : SRecords := {}

/-- The value of a symbolic evaluation and the term that holds when the evaluation throws. -/
abbrev SRes := SVal × Term

/-- Two string operands: the string, the searched string, and the term that holds when either throws or is no string. -/
def stringsOf (s p : SRes) : Term × Term × Term :=
  let (x, xe) := s.1.scalarOf
  let (y, ye) := p.1.scalarOf
  (.strOf x, .strOf y, .or s.2 (.or p.2 (.or xe (.or ye (.not (.and (.isStr x) (.isStr y)))))))

mutual

/-- The symbolic evaluation of `e`, as Ir.eval evaluates it, or why `e` has no encoding. -/
def seval (env : SEnv) (vars : List (String × SVal)) : Expr → Except String SRes
  | .undef => pure (.scalar undefT, ff)
  | .lit v => do pure (.scalar (← litTerm v), ff)
  | .arg a => pure ((env.args a).getD (.scalar undefT), ff)
  | .var x => match vars.lookup x with
    | some v => pure (v, ff)
    | none => pure (.scalar undefT, tt)
  | .let x e body => do
    let (v, ev) ← seval env vars e
    let (w, ew) ← seval env ((x, v) :: vars) body
    pure (w, .or ev ew)
  | .ite c yes no => do
    let (vc, ec) ← seval env vars c
    let (vy, ey) ← seval env vars yes
    let (vn, en) ← seval env vars no
    pure (.ite vc.truthy vy vn, .or ec (.ite vc.truthy ey en))
  | .and a b => do
    let (va, ea) ← seval env vars a
    let (vb, eb) ← seval env vars b
    pure (.ite va.truthy vb va, .or ea (.and va.truthy eb))
  | .or a b => do
    let (va, ea) ← seval env vars a
    let (vb, eb) ← seval env vars b
    pure (.ite va.truthy va vb, .or ea (.and (.not va.truthy) eb))
  | .coalesce a b => do
    let (va, ea) ← seval env vars a
    let (vb, eb) ← seval env vars b
    pure (.ite va.nullish vb va, .or ea (.and va.nullish eb))
  | .not a => do
    let (va, ea) ← seval env vars a
    pure (.scalar (.mkBool (.not va.truthy)), ea)
  | .eq a b => do
    let (va, ea) ← seval env vars a
    let (vb, eb) ← seval env vars b
    pure (.scalar (.mkBool (va.same vb)), .or ea eb)
  | .compare r .number a b => do
    let (va, ea) ← seval env vars a
    let (vb, eb) ← seval env vars b
    let (x, xe) := va.scalarOf
    let (y, ye) := vb.scalarOf
    pure (.scalar (.mkBool (relT r (.intOf x) (.intOf y))),
      .or ea (.or eb (.or xe (.or ye (.not (.and (.isInt x) (.isInt y)))))))
  | .compare r .date a b => do
    let (va, ea) ← seval env vars a
    let (vb, eb) ← seval env vars b
    let (x, xe) := va.scalarOf
    let (y, ye) := vb.scalarOf
    pure (.scalar (.mkBool (relT r (dayOf x) (dayOf y))),
      .or ea (.or eb (.or xe (.or ye (.not (.and (isDateOf x) (isDateOf y)))))))
  | .field o name => do
    let (v, e) ← seval env vars o
    pure (v.field env.records name, .or e v.nullish)
  | .fieldOpt o name => do
    let (v, e) ← seval env vars o
    pure (.ite v.nullish (.scalar undefT) (v.field env.records name), e)
  | .strLen s => do
    let (v, e) ← seval env vars s
    let (x, xe) := v.scalarOf
    pure (.scalar (.mkInt (.len (.strOf x))), .or e (.or xe (.not (.isStr x))))
  | .startsWith s p => do
    let rs ← seval env vars s
    let rp ← seval env vars p
    let (x, y, err) := stringsOf rs rp
    pure (.scalar (.mkBool (.prefixOf y x)), err)
  | .endsWith s p => do
    let rs ← seval env vars s
    let rp ← seval env vars p
    let (x, y, err) := stringsOf rs rp
    pure (.scalar (.mkBool (.suffixOf y x)), err)
  | .strIncludes s p => do
    let rs ← seval env vars s
    let rp ← seval env vars p
    let (x, y, err) := stringsOf rs rp
    pure (.scalar (.mkBool (.contains x y)), err)
  | .size c => do
    let (v, e) ← seval env vars c
    let (n, ne) := v.size env.records
    pure (n, .or e ne)
  | .table entity => pure (.table entity, ff)
  | .single entity => pure (.single entity, ff)
  | .lookup t k => do
    let (vt, et) ← seval env vars t
    let (vk, ek) ← seval env vars k
    let (v, e) := SVal.lookup env.records vk vt
    pure (v, .or et (.or ek e))
  | .obj fields => do
    let (fs, e) ← sevalFields env vars fields
    pure (.obj fs, e)
  | .arr values => do
    let (vs, e) ← sevalAll env vars values
    pure (.list vs, e)
  | .concat a b => do
    let (va, ea) ← seval env vars a
    let (vb, eb) ← seval env vars b
    match va, vb with
    | .list xs, .list ys => pure (.list (xs ++ ys), .or ea eb)
    | _, _ =>
      match va.items env.records, vb.items env.records with
      | some xs, some ys => pure (.bag (xs ++ ys), .or ea eb)
      | _, _ => throw "a concat of what may be no collection"
  | .includes a v => do
    let (va, ea) ← seval env vars a
    let (vv, ev) ← seval env vars v
    let (found, e) := SVal.includes vv va
    pure (.scalar (.mkBool found), .or ea (.or ev e))
  | .arith op a b => do
    let (va, ea) ← seval env vars a
    let (vb, eb) ← seval env vars b
    let (x, xe) := va.scalarOf
    let (y, ye) := vb.scalarOf
    pure (.scalar (.mkInt (arithT op (.intOf x) (.intOf y))),
      .or ea (.or eb (.or xe (.or ye (.not (.and (.isInt x) (.isInt y)))))))
  | .emit event payload => do
    let (v, e) ← seval env vars payload
    pure (.emit event v, e)
  | .filter _ c x body => do
    let (vc, ec) ← seval env vars c
    let some items := vc.items env.records | throw "a filter of what may be no collection"
    let visits ← items.mapM fun (g, v) => do pure (g, v, ← seval env ((x, v) :: vars) body)
    pure (.bag (visits.map fun (g, v, b, _) => (.and g b.truthy, v)), .or ec (thrownIn visits))
  | .some .bag c x body => do
    let (vc, ec) ← seval env vars c
    let some items := vc.items env.records | throw "a some of what may be no collection"
    let visits ← items.mapM fun (g, v) => do pure (g, v, ← seval env ((x, v) :: vars) body)
    pure (.scalar (.mkBool (disj (visits.map fun (g, _, b, _) => .and g (b.same trueT)))), .or ec (thrownIn visits))
  | .every .bag c x body => do
    let (vc, ec) ← seval env vars c
    let some items := vc.items env.records | throw "an every of what may be no collection"
    let visits ← items.mapM fun (g, v) => do pure (g, v, ← seval env ((x, v) :: vars) body)
    pure (.scalar (.mkBool (.not (disj (visits.map fun (g, _, b, _) => .and g (b.same falseT))))),
      .or ec (thrownIn visits))
  | .some .array .. => throw "an array's some"
  | .every .array .. => throw "an array's every"
  | .map _ c x body => do
    let (vc, ec) ← seval env vars c
    let some items := vc.items env.records | throw "a map of what may be no collection"
    let visits ← items.mapM fun (g, v) => do pure (g, v, ← seval env ((x, v) :: vars) body)
    pure (.bag (visits.map fun (g, _, b, _) => (g, b)), .or ec (thrownIn visits))
  | .sum c x body => do
    let (vc, ec) ← seval env vars c
    let some items := vc.items env.records | throw "a sum of what may be no collection"
    let visits ← items.mapM fun (g, v) => do pure (g, v, ← seval env ((x, v) :: vars) body)
    let (total, bad) := sumIn visits
    pure (.scalar (.mkInt total), .or ec (.or (thrownIn visits) (.or bad (.not (safeT total)))))
  | .min .number c x body => do
    let (vc, ec) ← seval env vars c
    let some items := vc.items env.records | throw "a min of what may be no collection"
    let visits ← items.mapM fun (g, v) => do pure (g, v, ← seval env ((x, v) :: vars) body)
    pure (.scalar (leastIn (fun k m => .lt (.intOf k) (.intOf m)) ff undefT visits),
      .or ec (.or (thrownIn visits) (keysBad visits)))
  | .max .number c x body => do
    let (vc, ec) ← seval env vars c
    let some items := vc.items env.records | throw "a max of what may be no collection"
    let visits ← items.mapM fun (g, v) => do pure (g, v, ← seval env ((x, v) :: vars) body)
    pure (.scalar (leastIn (fun k m => .lt (.intOf m) (.intOf k)) ff undefT visits),
      .or ec (.or (thrownIn visits) (keysBad visits)))
  | .min .date .. => throw "a min of dates"
  | .max .date .. => throw "a max of dates"
  | .only c => do
    let (vc, ec) ← seval env vars c
    let some items := vc.items env.records | throw "an only of what may be no collection"
    pure (firstIn items, .or ec (twoIn items))
  | .sortedBy .. => throw "sortedBy, whose groups the encoding does not hold"
  | .format .. => throw "a template literal"
  | .decimal .. => throw "decimal arithmetic"
  | .addDays d n => do
    let (vd, ed) ← seval env vars d
    let (vn, en) ← seval env vars n
    let (x, xe) := vd.scalarOf
    let (y, ye) := vn.scalarOf
    let day := Term.add (dayOf x) (.intOf y)
    pure (.scalar (.mkStr (.dateLabel day)),
      .or ed (.or en (.or xe (.or ye (.not (.and (isDateOf x) (.and (.isInt y) (inRangeT day))))))))
  | .createKey .. => throw "createKey"

def sevalAll (env : SEnv) (vars : List (String × SVal)) : List Expr → Except String (List SVal × Term)
  | [] => pure ([], ff)
  | e :: es => do
    let (v, ev) ← seval env vars e
    let (vs, evs) ← sevalAll env vars es
    pure (v :: vs, .or ev evs)

def sevalFields (env : SEnv) (vars : List (String × SVal)) : List Field → Except String (List (String × SVal) × Term)
  | [] => pure ([], ff)
  | ⟨name, e⟩ :: fs => do
    let (v, ev) ← seval env vars e
    let (vs, evs) ← sevalFields env vars fs
    pure ((name, v) :: vs, .or ev evs)

end

end Tazuna.Smt
