import Tazuna.Smt.StrCode

/-! Confirming a model of the abstract variant (`Script.abs`). The variant's model may be one no strings realize, so
the engine never reads it as the script's: it asks the exact script again with that model's values fixed, and reads
that answer, a model of the exact script, as it reads any. Two fixings, tried in order: every value fixed with each
code read as a string in the codes' order (strict; ground, so cheap), then only the values that are not strings
(loose; the solver chooses the strings, which a length rule needs). Nothing here is trusted: a fixing that the exact
script refutes only costs the question its abstraction. -/

namespace Tazuna.Smt

/-- `k` strings in increasing order strictly between `lo` and `hi` (none: no bound); none where fewer exist. Between
`s` and `s ++ "\u{0}"` there is none, so the order of strings is not dense; `fuel` bounds the recursion, which drops a
character of `hi` each time. -/
def between : Nat → Option (List Char) → Option (List Char) → Nat → Option (List (List Char))
  | _, _, _, 0 => some []
  | 0, _, _, _ => none
  | fuel + 1, none, hi, k + 1 =>
    if hi == some [] then none else (between fuel (some []) hi k).map ([] :: ·)
  | _, some lo, none, k => some ((List.range k).map fun j => lo ++ List.replicate (j + 1) 'z')
  | fuel + 1, some lo, some hi, k =>
    if lo.isPrefixOf hi then
      match hi.drop lo.length with
      | [] => none
      | r :: rs =>
        if 0 < r.toNat then some ((List.range k).map fun j => lo ++ Char.ofNat (r.toNat - 1) :: List.replicate j 'z')
        else if rs.isEmpty then none
        else (between fuel (some []) (some rs) k).map (·.map fun x => lo ++ '\x00' :: x)
    else if lo < hi then some ((List.range k).map fun j => lo ++ List.replicate (j + 1) 'z')
    else none

/-- A string for each code, in the codes' order, each literal's code its literal: the codes between two literals'
codes get strings between the literals where there are enough, the others strings after every string given. -/
def strictStrings (litCodes : List (Int × String)) (codes : List Int) : List (Int × String) := Id.run do
  let lits := litCodes.map fun (n, s) => (n, s.toList)
  let all := ((codes ++ lits.map (·.1)).toArray.qsort (· < ·)).toList.eraseDups
  let mut out : List (Int × List Char) := lits
  let mut left : List Int := []
  let mut lo : Option (List Char) := none
  let mut run : List Int := []
  for n in all do
    match lits.lookup n with
    | some s =>
      match between (s.length + 1) lo (some s) run.length with
      | some ss => out := out ++ run.zip ss
      | none => left := left ++ run
      lo := some s
      run := []
    | none => run := run ++ [n]
  match between 1 lo none run.length with
  | some ss => out := out ++ run.zip ss
  | none => left := left ++ run
  let top := out.foldl (fun m (_, s) => if m < s then s else m) []
  out := out ++ left.zipIdx.map fun (n, j) => (n, top ++ List.replicate (j + 1) 'z')
  return out.map fun (n, s) => (n, String.ofList s)

section
variable (dts : List Datatype)

mutual
/-- The exact script's term of sort `s` for the variant's value `w`, each string position's code by `str`; none where
`w` does not fit `s`. -/
def fixTerm (str : Int → Option Term) : Srt → Val → Option Term
  | .str, .int n => str n
  | .int, .int n => some (.int n)
  | .bool, .bool b => some (.bool b)
  | .dt _, .ctor e k ws => do
    let fs ← fieldsOf dts e k
    guard (fs.length = ws.length)
    pure (.ctor e k (← fixTerms str fs ws))
  | _, _ => none
def fixTerms (str : Int → Option Term) : List Srt → List Val → Option (List Term)
  | f :: fs, w :: ws => do pure ((← fixTerm str f w) :: (← fixTerms str fs ws))
  | _, _ => some []
end

mutual
/-- What fixes the parts of `t` that are not strings to the variant's value `w` at sort `s`. -/
def looseFix : Srt → Term → Val → List Term
  | .int, t, .int n => [.eq t (.int n)]
  | .bool, t, .bool b => [.eq t (.bool b)]
  | .dt _, t, .ctor e k ws => match fieldsOf dts e k with
    | some fs => .is e k t :: looseFixes e k t 0 fs ws
    | none => []
  | _, _, _ => []
def looseFixes (e k : Nat) (t : Term) : Nat → List Srt → List Val → List Term
  | j, f :: fs, w :: ws => looseFix f (.sel e k j t) w ++ looseFixes e k t (j + 1) fs ws
  | _, _, _ => []
end

/-- The codes at the string positions of the variant's value `w` at sort `s`. -/
def strCodes : Srt → Val → List Int
  | .str, .int n => [n]
  | .dt _, .ctor e k ws => match fieldsOf dts e k with
    | some fs => (fs.zip ws).attach.flatMap fun ⟨(f, w), _⟩ => strCodes f w
    | none => []
  | _, _ => []
decreasing_by
  have := List.of_mem_zip ‹_›
  have := List.sizeOf_lt_of_mem this.2
  simp_wf; omega

/-- The fixings to confirm the variant's model `vs` by, in the order to try: strict, where every value fits, then
loose. `vars` are the exact script's variables and `lits` its literals, whose variables the variant adds after
them. -/
def confirmations (vars : List Srt) (lits : List String) (vs : List (Nat × Val)) : List (List Term) :=
  let base := vars.length
  let inputs := vars.zipIdx.filterMap fun (s, n) => (vs.lookup n).map (n, s, ·)
  let litCodes := lits.zipIdx.filterMap fun (x, i) => match vs.lookup (base + i) with
    | some (.int n) => some (n, x)
    | _ => none
  let codes := inputs.flatMap fun (_, s, w) => strCodes dts s w
  let named := strictStrings litCodes codes
  let strict := inputs.mapM fun (n, s, w) =>
    (fixTerm dts (fun c => (named.lookup c).map Term.str) s w).map (Term.eq (.var n))
  let loose := inputs.flatMap fun (n, s, w) => looseFix dts s (.var n) w
  (if inputs.length = vars.length && litCodes.length = lits.length then strict.toList else []) ++ [loose]

end

end Tazuna.Smt
