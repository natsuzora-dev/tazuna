import Tazuna.Smt.Script
import Tazuna.Ir.Literal

/-! Names as codes. An id from outside (`named s`) is datatype `d`'s constructor 1, whose one field holds the name as
a string. A step reads a name only by comparing it: `=` and the canonical order's `str.<` (`idOrd`), which orders
the ids that start machines and fire timers. The solver's string theory is slow on such scripts, though no string
operation reaches the names, so the solver reads a variant of each script (`Term.code`) where that field is an Int
and the order on names is `<`. The variant refuses a script where a name meets any other operation, and the solver
then reads the script as it is.

`code_model` proves the variant has a model wherever the script has one: the names a model compares are finitely
many, so ranking them keeps both `=` and the order. An unsat answer to the variant thus says the script is unsat
(`Unsat`). A sat answer's values read back with the fixed name `nameOf n` of each code `n` (`Val.uncode`), which
keeps both `=` and the order (`nameOf_lt`), so each value decodes on its own; Lean then decodes and recomputes them as
it does any model's. -/

namespace Tazuna.Smt

/-- Whether the term selects the name of an id: field 0 of datatype `d`'s constructor 1. -/
def Term.isName (d : Nat) : Term → Bool
  | .shared _ t => t.isName d
  | .sel e k j _ => e == d && k == 1 && j == 0
  | _ => false

mutual
/-- The term with names as codes: `str.<` between names is `<`; none where a name meets another operation, a
constructor 1 of `d` is built, or a reference occurs. -/
def Term.code (d : Nat) : Term → Option Term
  | .var n => some (.var n)
  | .int n => some (.int n)
  | .str s => some (.str s)
  | .bool b => some (.bool b)
  | .ref _ => none
  | .not a => (a.code d).map .not
  | .len a => (a.code d).map .len
  | .and a b => do pure (.and (← a.code d) (← b.code d))
  | .or a b => do pure (.or (← a.code d) (← b.code d))
  | .lt a b => do pure (.lt (← a.code d) (← b.code d))
  | .le a b => do pure (.le (← a.code d) (← b.code d))
  | .add a b => do pure (.add (← a.code d) (← b.code d))
  | .sub a b => do pure (.sub (← a.code d) (← b.code d))
  | .mul a b => do pure (.mul (← a.code d) (← b.code d))
  | .div a b => do pure (.div (← a.code d) (← b.code d))
  | .mod a b => do pure (.mod (← a.code d) (← b.code d))
  | .cat a b => do pure (.cat (← a.code d) (← b.code d))
  | .eq a b =>
    if a.isName d && b.isName d then do pure (.eq (← a.codeName d) (← b.codeName d))
    else if a.isName d || b.isName d then none
    else do pure (.eq (← a.code d) (← b.code d))
  | .slt a b =>
    if a.isName d && b.isName d then do pure (.lt (← a.codeName d) (← b.codeName d))
    else if a.isName d || b.isName d then none
    else do pure (.slt (← a.code d) (← b.code d))
  | .ite c a b => do pure (.ite (← c.code d) (← a.code d) (← b.code d))
  | .ctor e k args => if e = d ∧ k = 1 then none else (Term.codes d args).map (.ctor e k)
  | .app f args => (Term.codes d args).map (.app f)
  | .is e k a => (a.code d).map (.is e k)
  | .sel e k j a => if e = d ∧ k = 1 then none else (a.code d).map (.sel e k j)
  | .shared h t => (t.code d).map (.shared h)
/-- A name term with names as codes. -/
def Term.codeName (d : Nat) : Term → Option Term
  | .shared h t => (t.codeName d).map (.shared h)
  | .sel e k j a => if e = d ∧ k = 1 ∧ j = 0 then (a.code d).map (.sel d 1 0) else none
  | _ => none
def Term.codes (d : Nat) : List Term → Option (List Term)
  | [] => some []
  | t :: ts => do pure ((← t.code d) :: (← Term.codes d ts))
end

/-! Coding with sharing. `Term.code` follows the tree, so a term whose shared parts nest costs time exponential in the
nesting. `Term.codeC` codes each shared term once, kept by its stored hash and confirmed by `Term.same`, so equal
shared terms also come out as one object, which the script's extraction finds at once; `codeC_ok` proves it is
`Term.code`, and `code_eq_codeFast` makes compiled code use it. -/

/-- Shared terms already coded, by the shared term's hash. -/
abbrev CodeCache := Std.HashMap UInt64 (List (Term × Term))

/-- Every entry of the cache is a shared term with its code. -/
def CodeCache.Ok (d : Nat) (c : CodeCache) : Prop :=
  ∀ (h : UInt64) (l : List (Term × Term)), c[h]? = some l → ∀ p ∈ l, p.1.code d = some p.2

def CodeCache.find? (c : CodeCache) (h : UInt64) (t : Term) : Option Term :=
  match c[h]? with
  | some l => (l.find? fun p => p.1.same t).map (·.2)
  | none => none

def CodeCache.add (c : CodeCache) (h : UInt64) (t t' : Term) : CodeCache :=
  match c[h]? with
  | some l => c.insert h ((t, t') :: l)
  | none => c.insert h [(t, t')]

mutual
/-- `Term.code` with each shared term coded once. -/
def Term.codeC (d : Nat) : Term → CodeCache → Option Term × CodeCache
  | .shared h t, c => match c.find? h (.shared h t) with
    | some t' => (some t', c)
    | none => match t.codeC d c with
      | (some t', c) => (some (.shared h t'), c.add h (.shared h t) (.shared h t'))
      | (none, c) => (none, c)
  | .var n, c => (some (.var n), c)
  | .int n, c => (some (.int n), c)
  | .str s, c => (some (.str s), c)
  | .bool b, c => (some (.bool b), c)
  | .ref _, c => (none, c)
  | .not a, c => let (x, c) := a.codeC d c; (x.map .not, c)
  | .len a, c => let (x, c) := a.codeC d c; (x.map .len, c)
  | .is e k a, c => let (x, c) := a.codeC d c; (x.map (.is e k), c)
  | .sel e k j a, c => if e = d ∧ k = 1 then (none, c) else let (x, c) := a.codeC d c; (x.map (.sel e k j), c)
  | .and a b, c => let (x, c) := a.codeC d c; let (y, c) := b.codeC d c; ((do pure (.and (← x) (← y))), c)
  | .or a b, c => let (x, c) := a.codeC d c; let (y, c) := b.codeC d c; ((do pure (.or (← x) (← y))), c)
  | .lt a b, c => let (x, c) := a.codeC d c; let (y, c) := b.codeC d c; ((do pure (.lt (← x) (← y))), c)
  | .le a b, c => let (x, c) := a.codeC d c; let (y, c) := b.codeC d c; ((do pure (.le (← x) (← y))), c)
  | .add a b, c => let (x, c) := a.codeC d c; let (y, c) := b.codeC d c; ((do pure (.add (← x) (← y))), c)
  | .sub a b, c => let (x, c) := a.codeC d c; let (y, c) := b.codeC d c; ((do pure (.sub (← x) (← y))), c)
  | .mul a b, c => let (x, c) := a.codeC d c; let (y, c) := b.codeC d c; ((do pure (.mul (← x) (← y))), c)
  | .div a b, c => let (x, c) := a.codeC d c; let (y, c) := b.codeC d c; ((do pure (.div (← x) (← y))), c)
  | .mod a b, c => let (x, c) := a.codeC d c; let (y, c) := b.codeC d c; ((do pure (.mod (← x) (← y))), c)
  | .cat a b, c => let (x, c) := a.codeC d c; let (y, c) := b.codeC d c; ((do pure (.cat (← x) (← y))), c)
  | .eq a b, c =>
    if a.isName d && b.isName d then
      let (x, c) := a.codeNameC d c; let (y, c) := b.codeNameC d c; ((do pure (.eq (← x) (← y))), c)
    else if a.isName d || b.isName d then (none, c)
    else let (x, c) := a.codeC d c; let (y, c) := b.codeC d c; ((do pure (.eq (← x) (← y))), c)
  | .slt a b, c =>
    if a.isName d && b.isName d then
      let (x, c) := a.codeNameC d c; let (y, c) := b.codeNameC d c; ((do pure (.lt (← x) (← y))), c)
    else if a.isName d || b.isName d then (none, c)
    else let (x, c) := a.codeC d c; let (y, c) := b.codeC d c; ((do pure (.slt (← x) (← y))), c)
  | .ite x a b, c =>
    let (x, c) := x.codeC d c
    let (a, c) := a.codeC d c
    let (b, c) := b.codeC d c
    (do pure (.ite (← x) (← a) (← b)), c)
  | .ctor e k args, c => if e = d ∧ k = 1 then (none, c) else let (xs, c) := Term.codesC d args c; (xs.map (.ctor e k), c)
  | .app f args, c => let (xs, c) := Term.codesC d args c; (xs.map (.app f), c)
def Term.codeNameC (d : Nat) : Term → CodeCache → Option Term × CodeCache
  | .shared h t, c => let (x, c) := t.codeNameC d c; (x.map (.shared h), c)
  | .sel e k j a, c => if e = d ∧ k = 1 ∧ j = 0 then let (x, c) := a.codeC d c; (x.map (.sel d 1 0), c) else (none, c)
  | _, c => (none, c)
def Term.codesC (d : Nat) : List Term → CodeCache → Option (List Term) × CodeCache
  | [], c => (some [], c)
  | t :: ts, c =>
    let (x, c) := t.codeC d c
    let (xs, c) := Term.codesC d ts c
    (do pure ((← x) :: (← xs)), c)
end

/-- The id datatype as the script declares it: fresh ids by two Ints, named ones by a string. -/
def idDatatype : Datatype := ⟨[[.int, .int], [.str]]⟩

/-- The id datatype with names as codes. -/
def codedIdDatatype : Datatype := ⟨[[.int, .int], [.int]]⟩

/-- The script with names as codes, `d` being the id datatype; none where `Term.code` refuses an assertion. -/
def Script.code (d : Nat) (s : Script) : Option Script := do
  guard (s.datatypes[d]? == some idDatatype)
  let asserts ← (Term.codesC d s.asserts {}).1
  pure { s with datatypes := s.datatypes.set d codedIdDatatype, asserts }

/-- What the solver reads for the script, `ids` being the id datatype if the script has one: the script with names as
codes where `Script.code` builds it, else the script. The assertions are first merged into one object per equal subterm
(`shareCommon'`, the identity on values), as in `Script.shared`: the coding and the abstract variant (`Script.abs`)
find a shared term they already did by `Term.same`, which answers at once for one object but compares two copies as
trees, in time exponential in how deeply shared terms nest. -/
def Script.sent (ids : Option Nat) (s : Script) : Script :=
  let s := { s with asserts := ShareCommon.shareCommon' s.asserts }
  match ids.bind (s.code ·) with
  | some s' => s'
  | none => s

/-! The fixed name of a code. -/

/-- The name of code `n`, in the order of the codes (`nameOf_lt`): a code from 0 is its decimal digits after one `~`
per digit past the first (`7`, `~42`, `~~100`), so a longer number sorts later; a code below 0 is `-`, one `!` per
digit past the first, then each digit of its magnitude as 9 less it (-1 is `-8`, -10 is `-!89`), so a larger
magnitude sorts earlier, and every such name before every name of a code from 0. -/
def nameOf (n : Int) : String :=
  match n with
  | .ofNat m =>
    let ds := Ir.Literal.decimalDigits m
    String.ofList (List.replicate (ds.length - 1) '~' ++ ds.map Ir.Literal.digitChar)
  | .negSucc m =>
    let ds := Ir.Literal.decimalDigits (m + 1)
    String.ofList ('-' :: List.replicate (ds.length - 1) '!' ++ ds.map fun d => Ir.Literal.digitChar (9 - d))

mutual
/-- The value with each code of a name in datatype `d` replaced by its name (`nameOf`). -/
def Val.uncode (d : Nat) : Val → Val
  | .ctor e k args =>
    match e == d && k == 1, args with
    | true, [.int n] => .ctor e k [.str (nameOf n)]
    | _, _ => .ctor e k (Val.uncodes d args)
  | v => v
def Val.uncodes (d : Nat) : List Val → List Val
  | [] => []
  | v :: vs => Val.uncode d v :: Val.uncodes d vs
end

end Tazuna.Smt
