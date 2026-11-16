import Tazuna.Data.Canonical
import Tazuna.Data.Trace

/-!
This module unifies two values under a renaming of strings: the peer check compares a peer's values with a scenario's,
where the peer may give a createKey value or a request id its own string, one-to-one.
-/

namespace Tazuna.Data

/-- Why unify gives no bindings. -/
inductive Unequal where
  /-- The values differ. -/
  | differ
  /-- A bag's search used up its tries before it found an order. -/
  | searchLimit
deriving DecidableEq, Repr, Inhabited

/-- The result of unifyBag with `searchLimit` tries: none left means that the search did not finish. -/
def searched : Except Nat Bindings → Except Unequal Bindings
  | .ok bs => .ok bs
  | .error 0 => .error .searchLimit
  | .error _ => .error .differ

mutual

/--
Whether the peer's value `s` can equal the scenario's value `t` under some bindings: unify's comparison with each
string of `created` equal to any string, and bags compared by their sizes.
-/
def fits (created : List String) : CValue → CValue → Bool
  | .leaf (.str v), .leaf (.str w) => created.contains v || w == v
  | .leaf v, .leaf w => w == v
  | .arr xs, .arr ys | .runs xs, .runs ys => fitsList created xs ys
  | .bag xs, .bag ys => xs.length == ys.length
  | .obj fs, .obj gs => sameKeys fs gs && fitsFields created fs gs
  | _, _ => false

def fitsList (created : List String) : List CValue → List CValue → Bool
  | x :: xs, y :: ys => fits created x y && fitsList created xs ys
  | [], [] => true
  | _, _ => false

def fitsFields (created : List String) : List (String × CValue) → List (String × CValue) → Bool
  | [], _ => true
  | (k, v) :: fs, gs => (gs.lookup k).any (fits created v) && fitsFields created fs gs

end

/--
Whether the elements of `ss` can pair one to one with those of `ts` as far as fits tells: the elements of `ss` that
fit the same elements of `ts` are no more than those elements. unify fails at once otherwise, before it searches.
-/
def bagFits (created : List String) (ss ts : List CValue) : Bool :=
  let fitting (s : CValue) : List Nat := ts.zipIdx.filterMap fun (t, k) => if fits created s t then some k else none
  ss.all fun s => (ss.filter (fitting · == fitting s)).length ≤ (fitting s).length

mutual

/--
`bs` extended so that the peer's value `s` equals the scenario's value `t`, or why not. A string of `created` equals the
string that it is bound to, and is bound when it is not (Bindings.bind); other strings equal themselves. Bags pair their
elements by backtracking, as verify's `free` does, after bagFits, with `searchLimit` tries each (unifyBag).
-/
def unify (created : List String) (s t : CValue) (bs : Bindings) : Except Unequal Bindings :=
  match s, t with
  | .leaf (.str v), t =>
    match t with
    | .leaf (.str w) =>
      if created.contains v then (bs.bind v w).elim (.error .differ) .ok
      else if w == v then .ok bs else .error .differ
    | _ => .error .differ
  | .leaf v, .leaf w => if w == v then .ok bs else .error .differ
  | .arr xs, .arr ys => if xs.length == ys.length then unifyList created xs ys bs else .error .differ
  | .runs xs, .runs ys => if xs.length == ys.length then unifyList created xs ys bs else .error .differ
  | .bag xs, .bag ys =>
    if bagFits created xs ys then searched (unifyBag created xs ys bs searchLimit) else .error .differ
  | .obj fs, .obj gs => if sameKeys fs gs then unifyFields created fs gs bs else .error .differ
  | _, _ => .error .differ
termination_by (sizeOf s, 0)
decreasing_by all_goals lex_decreasing

def unifyList (created : List String) (xs ys : List CValue) (bs : Bindings) : Except Unequal Bindings :=
  match xs, ys with
  | x :: xs, y :: ys => (unify created x y bs).bind (unifyList created xs ys)
  | _, _ => .ok bs
termination_by (sizeOf xs, 0)
decreasing_by all_goals lex_decreasing

/-- The fields in the field order of `fs`. -/
def unifyFields (created : List String) (fs gs : List (String × CValue)) (bs : Bindings) : Except Unequal Bindings :=
  match fs with
  | [] => .ok bs
  | (k, v) :: fs =>
    (gs.lookup k).elim (.error .differ) fun w => (unify created v w bs).bind (unifyFields created fs gs)
termination_by (sizeOf fs, 0)
decreasing_by all_goals lex_decreasing

/--
`bs` extended so that the elements of `ss` equal those of `ts` in some order, or, when no order is found within `left`
tries, the tries left. A try unifies an element of `ss` with an element of `ts`; a try whose own search did not finish
ends the search with none left.
-/
def unifyBag (created : List String) (ss ts : List CValue) (bs : Bindings) (left : Nat) : Except Nat Bindings :=
  if ss.length != ts.length then .error left
  else
    match ss with
    | [] => .ok bs
    | first :: rest => unifyBagFrom created first rest ts [] bs left
termination_by (sizeOf ss, ts.length + 1)
decreasing_by all_goals lex_decreasing

/-- The search of unifyBag for `first`. `passed` holds the candidates tried. -/
def unifyBagFrom (created : List String) (first : CValue) (rest cands passed : List CValue) (bs : Bindings)
    (left : Nat) : Except Nat Bindings :=
  match cands, left with
  | [], left => .error left
  | _ :: _, 0 => .error 0
  | t :: more, left + 1 =>
    match unify created first t bs with
    | .ok bs' =>
      match unifyBag created rest (passed.reverse ++ more) bs' left with
      | .ok bs'' => .ok bs''
      | .error left' => unifyBagFrom created first rest more (t :: passed) bs left'
    | .error .searchLimit => .error 0
    | .error .differ => unifyBagFrom created first rest more (t :: passed) bs left
termination_by (sizeOf first + sizeOf rest + 1, cands.length)
decreasing_by all_goals lex_decreasing

end

/--
`bs` extended so that the mock's answer `a` is the peer's answer `b`, the peer's values in the form `seen` and the
mock's in the form `form`, or why not. Rejections compare by kind, as verify compares them.
-/
def unifyAnswer (created : List String) (seen form : Value → CValue) (bs : Bindings) :
    Answer → Answer → Except Unequal Bindings
  | .accepted (some x), .accepted (some y) => unify created (seen x) (form y) bs
  | .accepted none, .accepted none => .ok bs
  | .fulfilled x, .fulfilled y => unify created (seen x) (form y) bs
  | .rejected r, .rejected q => if r.kind == q.kind then .ok bs else .error .differ
  | _, _ => .error .differ

end Tazuna.Data
