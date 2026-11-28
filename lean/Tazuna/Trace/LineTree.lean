import Tazuna.Trace.Run
import Tazuna.Trace.Cands

/-! Out lines as trees, the form verify compares them in. The spec's expected lines become trees with the spec's ids and
wire ids at their leaves (`Expect.tree`); a trace's out line, read with the type of its value, becomes a tree with the
trace's names there (`lineTree`). Verify matches a trace line to an expected line when the two trees are the same once
a binding names the keys (`TreeW`), which is what the line writes by decoding (`LineW`, `lineW_iff`). -/

namespace Tazuna.Trace

open Tazuna.Ir Tazuna.Ir.Step

/-- Types compare by `Ty.same`, which decides equality (`same_eq`, `Ty_same_self`). -/
instance : DecidableEq Ty := fun a b =>
  if h : (Ty.same a b).isSome then isTrue (same_eq h) else isFalse fun e => h (e ▸ Ty_same_self a)

/-- A Bool's or Nil's wire form as an atom. -/
def litTree {α : Type} : Wire → Option (Tree α)
  | .bool b => some (.atom (.atom (if b then "true" else "false")))
  | .null => some (.atom (.atom "nil"))
  | _ => none

section
variable (T : List TypeDecl)

-- A type index past the table has no variants, so no tag matches.
set_option linter.tazuna.silentDefault false in
mutual
/-- The tree of a value of type `t`, with its ids at the leaves, where it has a wire form. -/
def valTree : (t : Ty) → t.den0 → Option (Tree Key)
  | .int, n => some (.atom (.int n))
  | .str, s => some (.atom (.bin s.1))
  | .list t, xs => (xs.mapM (valTree t)).map .seq
  | .bag t, xs => (xs.mapM (valTree t)).map .bag
  | .tuple ts, x => (valTrees ts x).map .seq
  | .adt i _ vs, x =>
    if i = 0 then (encBool vs x).bind litTree else if i = 1 then (encNil vs x).bind litTree
    else valAlts ((T[i]?.map (·.variants)).getD []) 0 vs x
  | .table k v, x => (x.1.mapM fun (a, b) => do pure (Tree.seq [← valTree k a, ← valTree v b])).map .bag
  | .point .day, d => some (.atom (.bin (renderDate d)))
  | .point .ms, n => some (.atom (.int n))
  | .id, n => some (.leaf (.id n))
  | .fn .., _ | .param _, _ | .dsl .., _ => none
def valTrees : (ts : List Ty) → (Ty.semsWith Dsl.base ts).1 → Option (List (Tree Key))
  | [], () => some []
  | t :: ts, (x, xs) => do pure ((← valTree t x) :: (← valTrees ts xs))
/-- A value of the variants `vs`, which are the declaration's variants from index `k` on: its tag, then its fields. -/
def valAlts (decl : List Variant) (k : Nat) : (vs : List (List Ty)) → (Ty.semAltsWith Dsl.base vs).1 → Option (Tree Key)
  | [], x => nomatch x
  | fs :: _, .inl x => do
    let var ← decl[k]?
    let ts ← valTrees fs x
    if writable decl k var && (fieldKeys var.fields).length == ts.length then pure (.seq (.atom (.bin var.name) :: ts))
    else none
  | _ :: vs, .inr y => valAlts decl (k + 1) vs y
end

-- A type index past the table has no variants, so no tag matches.
set_option linter.tazuna.silentDefault false in
mutual
/-- The tree of a wire form read as type `t`, with the names at id positions at the leaves. -/
def wireTree : (t : Ty) → Wire → Option (Tree Name)
  | .int, .num n => some (.atom (.int n))
  | .str, .str s => some (.atom (.bin s))
  | .list t, .arr ws => (ws.mapM (wireTree t)).map .seq
  | .bag t, .arr ws => (ws.mapM (wireTree t)).map .bag
  | .tuple ts, .arr ws => (wireTrees ts ws).map .seq
  | .adt i _ vs, w =>
    if i = 0 then (if (decBool vs w).isSome then litTree w else none)
    else if i = 1 then (if (decNil vs w).isSome then litTree w else none)
    else match w with
      | .obj kvs => do
        let decl := (T[i]?.map (·.variants)).getD []
        let .str tag ← kvs.lookup "tag" | none
        let k ← decl.findIdx? (·.name == tag)
        wireAlts decl kvs k 0 vs
      | _ => none
  | .table k v, .arr ws => (ws.mapM fun (w : Wire) => match w with
      | .arr [a, b] => do pure (Tree.seq [← wireTree k a, ← wireTree v b])
      | _ => none).map .bag
  | .point .day, .str s => some (.atom (.bin s))
  | .point .ms, .num n => some (.atom (.int n))
  | .id, .str s => some (.leaf (.id s))
  | _, _ => none
def wireTrees : (ts : List Ty) → List Wire → Option (List (Tree Name))
  | [], [] => some []
  | t :: ts, w :: ws => do pure ((← wireTree t w) :: (← wireTrees ts ws))
  | _, _ => none
/-- The fields of `fs` under `keys` in `kvs`. -/
def wireFields (kvs : List (String × Wire)) : (fs : List Ty) → List String → Option (List (Tree Name))
  | [], [] => some []
  | f :: fs, key :: keys => do pure ((← wireTree f (← kvs.lookup key)) :: (← wireFields kvs fs keys))
  | _, _ => none
/-- Variant `k` of the variants `vs`, which are the declaration's variants from index `j` on: its tag, then its fields,
with no key beside them. -/
def wireAlts (decl : List Variant) (kvs : List (String × Wire)) (k : Nat) (j : Nat) :
    (vs : List (List Ty)) → Option (Tree Name)
  | [] => none
  | fs :: vs =>
    if k = j then do
      let var ← decl[j]?
      let keys := fieldKeys var.fields
      if kvs.length = keys.length + 1 then pure (.seq (.atom (.bin var.name) :: (← wireFields kvs fs keys)))
      else none
    else wireAlts decl kvs k (j + 1) vs
end

variable (v : ServiceV)

/-- An out line the spec expects. -/
inductive Expect where
  | answered (to : String) (outcome : Outcome)
  | applied (event : v.event.den0)
  | sent (id : Nat) (external name : String) (input : WireVal)

-- No answer target means no answered line.
set_option linter.tazuna.silentDefault false in
/-- The out lines the spec expects of a step's result. -/
def expects (answerTo : Option String) (r : Result v) : List (Expect v) :=
  (answerTo.map fun to => [Expect.answered to r.outcome]).getD [] ++ r.events.map .applied ++
    r.out.map fun o => .sent o.id o.external o.name o.input

-- Message text: an unbound wire id prints as `?<id>`.
set_option linter.tazuna.silentDefault false in
/-- The expected out line, written with the binding so far. -/
def Expect.toLine (now : Int) (ids : List (IdV × String)) (wires : List (Nat × String)) : Expect v → Option Line
  | .answered to o => match o with
    | .accepted => some (.answered now to .accepted)
    | .answered ⟨t, x⟩ => (enc T (ids.lookup ·) t x).map fun w => .answered now to (.answered w)
    | .rejected ⟨t, x⟩ => (enc T (ids.lookup ·) t x).map fun w => .answered now to (.rejected w)
    | .invalid rs => some (.answered now to (.invalid rs))
    | .fault _ => none
  | .applied ev => (enc T (ids.lookup ·) v.event ev).map (.applied now)
  | .sent id x n ⟨t, i⟩ => (enc T (ids.lookup ·) t i).map (.sent now ((wires.lookup id).getD s!"?{id}") x n)

def outcomeTag : Outcome → String
  | .accepted => "accepted"
  | .answered _ => "answered"
  | .rejected _ => "rejected"
  | .invalid _ => "invalid"
  | .fault _ => "fault"

def answerTag : Answer → String
  | .accepted => "accepted"
  | .answered _ => "answered"
  | .rejected _ => "rejected"
  | .invalid _ => "invalid"

/-- What an expected line shows beside its values: its kind, its time and the names it carries as data. -/
def Expect.head (now : Int) : Expect v → List Erl
  | .answered to o => [.atom "answer", .int now, .bin to, .atom (outcomeTag o)]
  | .applied _ => [.atom "event", .int now]
  | .sent _ x n _ => [.atom "request", .int now, .bin x, .bin n]

/-- The type of an expected line's value, if it has one. -/
def Expect.ty : Expect v → Option Ty
  | .answered _ (.answered ⟨t, _⟩) | .answered _ (.rejected ⟨t, _⟩) => some t
  | .answered _ _ => none
  | .applied _ => some v.event
  | .sent _ _ _ ⟨t, _⟩ => some t

/-- The trees after an expected line's head: its value, and a sent request's wire id. -/
def Expect.body : Expect v → Option (List (Tree Key))
  | .answered _ .accepted => some []
  | .answered _ (.answered ⟨t, x⟩) | .answered _ (.rejected ⟨t, x⟩) => (valTree T t x).map ([·])
  | .answered _ (.invalid rs) => some [.bag (rs.map (.atom ∘ .bin))]
  | .answered _ (.fault _) => none
  | .applied ev => (valTree T v.event ev).map ([·])
  | .sent id _ _ ⟨t, i⟩ => (valTree T t i).map fun tr => [.leaf (.wire id), tr]

def Expect.tree (now : Int) (e : Expect v) : Option (Tree Key) :=
  (e.body T v).map fun b => .seq [.seq ((e.head v now).map .atom), .seq b]

end

/-- What an out line shows beside its values, as `Expect.head` reads it. -/
def Line.head : Line → Option (List Erl)
  | .answered t to a => some [.atom "answer", .int t, .bin to, .atom (answerTag a)]
  | .applied t _ => some [.atom "event", .int t]
  | .sent t _ x n _ => some [.atom "request", .int t, .bin x, .bin n]
  | _ => none

section
variable (T : List TypeDecl)

/-- The trees after an out line's head, its value read as `ty`. -/
def Line.body (ty : Option Ty) : Line → Option (List (Tree Name))
  | .answered _ _ .accepted => some []
  | .answered _ _ (.answered w) | .answered _ _ (.rejected w) | .applied _ w =>
    ty.bind fun t => (wireTree T t w).map ([·])
  | .answered _ _ (.invalid rs) => some [.bag (rs.map (.atom ∘ .bin))]
  | .sent _ id _ _ w => ty.bind fun t => (wireTree T t w).map fun tr => [.leaf (.wire id), tr]
  | _ => none

/-- An out line's tree, its value read as `ty`. -/
def lineTree (ty : Option Ty) (l : Line) : Option (Tree Name) := do
  pure (.seq [.seq ((← l.head).map .atom), .seq (← l.body T ty)])

variable (v : ServiceV)

/-- The trace line `l` matches the expected line `e` with the keys named by `β`: read with the type of `e`'s value, its
tree is `e`'s once `β` names `e`'s keys, up to the order of bag and table items. -/
def TreeW (β : Key → Name) (now : Int) (e : Expect v) (l : Line) : Prop :=
  ∃ te tl, e.tree T v now = some te ∧ lineTree T (Expect.ty v e) l = some tl ∧ Tree.Same (te.map β) tl

end

end Tazuna.Trace
