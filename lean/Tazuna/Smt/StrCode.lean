import Tazuna.Smt.NameCode

/-! Strings as codes. z3's string theory is slow on most scripts of a realistic spec, though most strings there are
only compared, or put together for an output nobody constrains. So the solver first reads an abstract variant of each
script (`Script.abs`): every string is an Int, each literal a variable, the order `str.<` is `<`, and `str.++` and
`str.len` are uninterpreted functions (`u0`, `u1`). Literal variables keep the literals' order, so a script that only
compares strings loses nothing.

The variant over-approximates: `abs_model` proves it has a model wherever the script has one, coding the finitely many
strings a model compares by their rank, so an unsat answer to it says the script is unsat (`Unsat`). A sat answer may
come from a model no strings realize, so it is never read as the script's: the engine first asks the exact script
again with the variant's model fixed (over-approximate, confirm, fall back; no refinement loop, so not CEGAR).

The coding of values follows the sorts the script declares (`scodeV`), so it is injective at each sort for every
value, a string and an Int alike: the variant reads as the script does in any model (`scode_denote`), with no proof
that each subterm's value has its sort. -/

namespace Tazuna.Smt

/-- A sort with strings as codes. -/
def Srt.code : Srt → Srt
  | .str => .int
  | s => s

/-- A datatype with strings as codes. -/
def Datatype.code (d : Datatype) : Datatype := ⟨d.ctors.map (·.map Srt.code)⟩

/-- The field sorts of constructor `k` of datatype `d`. -/
def fieldsOf (dts : List Datatype) (d k : Nat) : Option (List Srt) := dts[d]?.bind (·.ctors[k]?)

section
variable (dts : List Datatype)

/-- A coded argument as one of sort `sa` under `f`, of sort `sr`. -/
def scode1 (f : Term → Term) (sa sr : Srt) : Option (Term × Srt) → Option (Term × Srt)
  | some (a, s) => if s = sa then some (f a, sr) else none
  | none => none

/-- Two coded arguments of sorts `sa` and `sb` as one under `f`, of sort `sr`. -/
def scode2 (f : Term → Term → Term) (sa sb sr : Srt) : Option (Term × Srt) → Option (Term × Srt) → Option (Term × Srt)
  | some (a, s), some (b, s') => if s = sa ∧ s' = sb then some (f a b, sr) else none
  | _, _ => none

def scodeEq : Option (Term × Srt) → Option (Term × Srt) → Option (Term × Srt)
  | some (a, s), some (b, s') => if s = s' then some (.eq a b, .bool) else none
  | _, _ => none

def scodeIte : Option (Term × Srt) → Option (Term × Srt) → Option (Term × Srt) → Option (Term × Srt)
  | some (c, sc), some (a, s), some (b, s') => if sc = .bool ∧ s = s' then some (.ite c a b, s) else none
  | _, _, _ => none

def scodeCtor (e k : Nat) : Option (List (Term × Srt)) → Option (Term × Srt)
  | some ps => if fieldsOf dts e k = some (ps.map (·.2)) then some (.ctor e k (ps.map (·.1)), .dt e) else none
  | none => none

def scodeIs (e k : Nat) : Option (Term × Srt) → Option (Term × Srt)
  | some (a, s) => if s = .dt e then some (.is e k a, .bool) else none
  | none => none

def scodeSel (e k j : Nat) : Option (Term × Srt) → Option (Term × Srt)
  | some (a, s) => if s = .dt e then (fieldSrt? dts e k j).map fun f => (.sel e k j a, f) else none
  | none => none

def scodeCons : Option (Term × Srt) → Option (List (Term × Srt)) → Option (List (Term × Srt))
  | some p, some ps => some (p :: ps)
  | _, _ => none

end

mutual
/-- The term with strings as codes, with its sort before coding: a literal `s` is the variable `lit s`, `str.<` is `<`,
`str.++` is `u0` and `str.len` is `u1`. None where the term is not well sorted in `dts` and `vars`, a literal has no
variable, or a reference or a function occurs. -/
def Term.scode (dts : List Datatype) (vars : List Srt) (lit : String → Option Nat) : Term → Option (Term × Srt)
  | .var n => vars[n]?.map fun s => (.var n, s)
  | .int n => some (.int n, .int)
  | .bool b => some (.bool b, .bool)
  | .str s => (lit s).map fun i => (.var i, .str)
  | .ref _ | .app .. => none
  | .not a => scode1 .not .bool .bool (a.scode dts vars lit)
  | .len a => scode1 (fun a => .app 1 [a]) .str .int (a.scode dts vars lit)
  | .and a b => scode2 .and .bool .bool .bool (a.scode dts vars lit) (b.scode dts vars lit)
  | .or a b => scode2 .or .bool .bool .bool (a.scode dts vars lit) (b.scode dts vars lit)
  | .lt a b => scode2 .lt .int .int .bool (a.scode dts vars lit) (b.scode dts vars lit)
  | .le a b => scode2 .le .int .int .bool (a.scode dts vars lit) (b.scode dts vars lit)
  | .add a b => scode2 .add .int .int .int (a.scode dts vars lit) (b.scode dts vars lit)
  | .sub a b => scode2 .sub .int .int .int (a.scode dts vars lit) (b.scode dts vars lit)
  | .mul a b => scode2 .mul .int .int .int (a.scode dts vars lit) (b.scode dts vars lit)
  | .div a b => scode2 .div .int .int .int (a.scode dts vars lit) (b.scode dts vars lit)
  | .mod a b => scode2 .mod .int .int .int (a.scode dts vars lit) (b.scode dts vars lit)
  | .cat a b => scode2 (fun a b => .app 0 [a, b]) .str .str .str (a.scode dts vars lit) (b.scode dts vars lit)
  | .slt a b => scode2 .lt .str .str .bool (a.scode dts vars lit) (b.scode dts vars lit)
  | .eq a b => scodeEq (a.scode dts vars lit) (b.scode dts vars lit)
  | .ite c a b => scodeIte (c.scode dts vars lit) (a.scode dts vars lit) (b.scode dts vars lit)
  | .ctor e k args => scodeCtor dts e k (Term.scodes dts vars lit args)
  | .is e k a => scodeIs e k (a.scode dts vars lit)
  | .sel e k j a => scodeSel dts e k j (a.scode dts vars lit)
  | .shared h t => (t.scode dts vars lit).map fun (t, s) => (.shared h t, s)
def Term.scodes (dts : List Datatype) (vars : List Srt) (lit : String → Option Nat) :
    List Term → Option (List (Term × Srt))
  | [] => some []
  | t :: ts => scodeCons (t.scode dts vars lit) (Term.scodes dts vars lit ts)
end

/-! Coding with sharing, as `Term.codeC` codes names: each shared term once, so equal shared terms come out as one
object (`scodeC_ok`). -/

/-- Shared terms already coded, by the shared term's hash. -/
abbrev SCodeCache := Std.HashMap UInt64 (List (Term × Option (Term × Srt)))

/-- Every entry of the cache is a shared term with its code. -/
def SCodeCache.Ok (dts : List Datatype) (vars : List Srt) (lit : String → Option Nat) (c : SCodeCache) : Prop :=
  ∀ (h : UInt64) (l : List (Term × Option (Term × Srt))), c[h]? = some l → ∀ p ∈ l, p.1.scode dts vars lit = p.2

def SCodeCache.find? (c : SCodeCache) (h : UInt64) (t : Term) : Option (Option (Term × Srt)) :=
  match c[h]? with
  | some l => (l.find? fun p => p.1.same t).map (·.2)
  | none => none

def SCodeCache.add (c : SCodeCache) (h : UInt64) (t : Term) (r : Option (Term × Srt)) : SCodeCache :=
  match c[h]? with
  | some l => c.insert h ((t, r) :: l)
  | none => c.insert h [(t, r)]

section
variable (dts : List Datatype) (vars : List Srt) (lit : String → Option Nat)

mutual
/-- `Term.scode` with each shared term coded once. -/
def Term.scodeC : Term → SCodeCache → Option (Term × Srt) × SCodeCache
  | .shared h t, c => match c.find? h (.shared h t) with
    | some r => (r, c)
    | none => let (r, c) := t.scodeC c
      let r := r.map fun (t, s) => (.shared h t, s)
      (r, c.add h (.shared h t) r)
  | .not a, c => let (x, c) := a.scodeC c; (scode1 .not .bool .bool x, c)
  | .len a, c => let (x, c) := a.scodeC c; (scode1 (fun a => .app 1 [a]) .str .int x, c)
  | .and a b, c => let (x, c) := a.scodeC c; let (y, c) := b.scodeC c; (scode2 .and .bool .bool .bool x y, c)
  | .or a b, c => let (x, c) := a.scodeC c; let (y, c) := b.scodeC c; (scode2 .or .bool .bool .bool x y, c)
  | .lt a b, c => let (x, c) := a.scodeC c; let (y, c) := b.scodeC c; (scode2 .lt .int .int .bool x y, c)
  | .le a b, c => let (x, c) := a.scodeC c; let (y, c) := b.scodeC c; (scode2 .le .int .int .bool x y, c)
  | .add a b, c => let (x, c) := a.scodeC c; let (y, c) := b.scodeC c; (scode2 .add .int .int .int x y, c)
  | .sub a b, c => let (x, c) := a.scodeC c; let (y, c) := b.scodeC c; (scode2 .sub .int .int .int x y, c)
  | .mul a b, c => let (x, c) := a.scodeC c; let (y, c) := b.scodeC c; (scode2 .mul .int .int .int x y, c)
  | .div a b, c => let (x, c) := a.scodeC c; let (y, c) := b.scodeC c; (scode2 .div .int .int .int x y, c)
  | .mod a b, c => let (x, c) := a.scodeC c; let (y, c) := b.scodeC c; (scode2 .mod .int .int .int x y, c)
  | .cat a b, c => let (x, c) := a.scodeC c; let (y, c) := b.scodeC c
    (scode2 (fun a b => .app 0 [a, b]) .str .str .str x y, c)
  | .slt a b, c => let (x, c) := a.scodeC c; let (y, c) := b.scodeC c; (scode2 .lt .str .str .bool x y, c)
  | .eq a b, c => let (x, c) := a.scodeC c; let (y, c) := b.scodeC c; (scodeEq x y, c)
  | .ite x a b, c =>
    let (x, c) := x.scodeC c
    let (y, c) := a.scodeC c
    let (z, c) := b.scodeC c
    (scodeIte x y z, c)
  | .ctor e k args, c => let (xs, c) := Term.scodesC args c; (scodeCtor dts e k xs, c)
  | .is e k a, c => let (x, c) := a.scodeC c; (scodeIs e k x, c)
  | .sel e k j a, c => let (x, c) := a.scodeC c; (scodeSel dts e k j x, c)
  | t, c => (t.scode dts vars lit, c)
def Term.scodesC : List Term → SCodeCache → Option (List (Term × Srt)) × SCodeCache
  | [], c => (some [], c)
  | t :: ts, c =>
    let (x, c) := t.scodeC c
    let (xs, c) := Term.scodesC ts c
    (scodeCons x xs, c)
end

end

/-! The string literals of a script, found once per shared term. A literal missing here has no variable, so the
script then has no abstract variant; nothing else rests on the search. -/

mutual
def Term.litsInto : Term → Std.HashSet UInt64 × Std.HashSet String → Std.HashSet UInt64 × Std.HashSet String
  | .str s, (seen, acc) => (seen, acc.insert s)
  | .shared h t, (seen, acc) => if seen.contains h then (seen, acc) else t.litsInto (seen.insert h, acc)
  | .not a, st | .len a, st | .is _ _ a, st | .sel _ _ _ a, st => a.litsInto st
  | .and a b, st | .or a b, st | .eq a b, st | .lt a b, st | .le a b, st | .add a b, st | .sub a b, st
  | .mul a b, st | .div a b, st | .mod a b, st | .cat a b, st | .slt a b, st => b.litsInto (a.litsInto st)
  | .ite c a b, st => b.litsInto (a.litsInto (c.litsInto st))
  | .ctor _ _ args, st | .app _ args, st => Term.litsIntos args st
  | .var _, st | .int _, st | .bool _, st | .ref _, st => st
def Term.litsIntos : List Term → Std.HashSet UInt64 × Std.HashSet String → Std.HashSet UInt64 × Std.HashSet String
  | [], st => st
  | t :: ts, st => Term.litsIntos ts (t.litsInto st)
end

/-- The script's string literals in their order, each once. -/
def Script.lits (s : Script) : List String :=
  ((Term.litsIntos s.asserts ({}, {})).2.toArray.qsort (· < ·)).toList

/-- Whether the script holds strings: a string sort, or a literal. -/
def Script.hasStrings (s : Script) (lits : List String) : Bool :=
  !lits.isEmpty || s.vars.contains .str || s.datatypes.any (·.ctors.any (·.contains .str))

/-- The variable of literal `x` among `lits`, the variables after the script's own `base` of them. -/
def litVar (lits : List String) (base : Nat) (x : String) : Option Nat := (lits.idxOf? x).map (base + ·)

/-- Each literal's variable below the next literal's, so the codes keep the literals' order. -/
def litOrder (lits : List String) (base : Nat) : List Term :=
  (lits.zip (lits.drop 1)).filterMap fun (a, b) =>
    if a < b then do pure (.lt (.var (← litVar lits base a)) (.var (← litVar lits base b))) else none

/-- The script with strings as codes (`Term.scode`), declaring `u0` (`str.++`) and `u1` (`str.len`) and the literals'
variables after its own, all of which a sat answer shows; none where the script holds no strings, declares functions,
or an assertion has no variant or is not a Bool. -/
def Script.abs (s : Script) : Option Script := do
  guard s.funs.isEmpty
  let lits := s.lits
  guard (s.hasStrings lits)
  let base := s.vars.length
  let ps ← (Term.scodesC s.datatypes s.vars (litVar lits base) s.asserts {}).1
  guard (ps.all (·.2 == .bool))
  let vars := s.vars.map Srt.code ++ lits.map fun _ => Srt.int
  let asserts := ps.map (·.1) ++ litOrder lits base
  pure ⟨s.datatypes.map Datatype.code, vars, [2, 1], asserts, List.range (base + lits.length)⟩

end Tazuna.Smt
