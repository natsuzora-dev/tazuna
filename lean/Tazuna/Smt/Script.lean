import Tazuna.Smt.Share
import Tazuna.Smt.Syntax

/-! A script is one question to the solver in standard SMT-LIB 2.6: declarations, definitions of its shared terms,
assertions, a plain `(check-sat)` and, for a sat answer, the values of the variables it asks for. The answer names
each value by its variable, so a caller reads values by name, never by position. -/

namespace Tazuna.Smt

def Srt.text : Srt → String
  | .int => "Int"
  | .bool => "Bool"
  | .str => "String"
  | .dt i => s!"D{i}"

def Datatype.text (i : Nat) (d : Datatype) : String :=
  let ctor (k : Nat) (fs : List Srt) : String :=
    let fields := fs.zipIdx.map fun (f, j) => s!" ({(Name.sel i k j).text} {f.text})"
    s!"({(Name.ctor i k).text}{String.join fields})"
  s!"(declare-datatypes ((D{i} 0)) (({" ".intercalate (d.ctors.zipIdx.map fun (fs, k) => ctor k fs)})))"

/-- The sort of a term, given the sorts of the datatypes' fields, of the variables and of the definitions. -/
def Term.srt? (dts : List Datatype) (vars : List Srt) (defs : Array Srt) : Term → Option Srt
  | .var n => vars[n]?
  | .ref i => defs[i]?
  | .int _ | .add .. | .sub .. | .mul .. | .div .. | .mod .. | .len _ => some .int
  | .str _ | .cat .. => some .str
  | .bool _ | .not _ | .and .. | .or .. | .eq .. | .lt .. | .le .. | .slt .. | .is .. => some .bool
  | .ite _ a _ | .shared _ a => a.srt? dts vars defs
  | .ctor d _ _ => some (.dt d)
  | .app .. => some .int
  | .sel d k j _ => do (← (← (← dts[d]?).ctors[k]?)[j]?)

structure Script where
  /-- Datatype `i` may refer only to datatypes before it. -/
  datatypes : List Datatype := []
  /-- The sort of each variable `v<n>`, by `n`. -/
  vars : List Srt := []
  /-- The number of arguments of each function `u<f>`, by `f`; each takes Ints and gives an Int. -/
  funs : List Nat := []
  asserts : List Term := []
  /-- The variables whose values a sat answer reports. -/
  shows : List Nat := []

/-- The assertions with shared terms as references, and the bodies of the definitions with their sorts, in order.
`none` when a body has no sort, which the encoding never builds, or when an assertion holds a reference itself: such a
script is never sent, as `NoModel` records (`refFree`). Lean's runtime first merges equal subterms into one object
(`shareCommon'`, hash-consing; it is the identity on values), so two equal shared terms are one object and
`Term.same` answers at once, wherever and however often the encoder built them. -/
def Script.shared (s : Script) : Option (List Term × List (Term × Srt)) := do
  let asserts := ShareCommon.shareCommon' s.asserts
  guard (Term.refFrees asserts)
  let (asserts, D) := Term.extracts asserts {}
  let sorts ← D.entries.foldlM (fun acc (_, b) => do pure (acc.push (← b.srt? s.datatypes s.vars acc))) #[]
  pure (asserts, (D.entries.toList.map (·.2)).zip sorts.toList)

/-- The line defining `s<i>` as the body `b` of the sort `srt`. -/
def defineLine (i : Nat) (b : Term) (srt : Srt) : String := s!"(define-fun {(Name.def_ i).text} () {srt.text} {b.print})"

/-- A script's text in three parts, each a run of whole lines: the header, declarations and definitions; the
assertions; the check and the values asked for. -/
structure TextParts where
  head : String
  body : String
  tail : String

def TextParts.text (p : TextParts) : String := p.head ++ p.body ++ p.tail

/-- Lines as text, each ended by a line break. -/
def linesText (ls : List String) : String := String.join (ls.map (· ++ "\n"))

/-- The script's text after the solver's header lines, in parts, from its shared assertions and definitions. -/
def Script.parts (s : Script) (header : List String) (asserts : List Term) (defs : List (Term × Srt)) : TextParts :=
  { head := linesText (header ++ ["(set-option :produce-models true)", "(set-logic ALL)"] ++
      s.datatypes.zipIdx.map (fun (d, i) => d.text i) ++
      s.funs.zipIdx.map (fun (n, f) => s!"(declare-fun {(Name.fn f).text} ({" ".intercalate (List.replicate n "Int")}) Int)") ++
      s.vars.zipIdx.map (fun (srt, n) => s!"(declare-const {(Name.var n).text} {srt.text})") ++
      defs.zipIdx.map (fun ((b, srt), i) => defineLine i b srt))
    body := linesText (asserts.map (fun t => s!"(assert {t.print})"))
    tail := linesText (["(check-sat)"] ++ (if s.shows.isEmpty then [] else
      [s!"(get-value ({" ".intercalate (s.shows.map fun n => (Name.var n).text)}))"])) }

/-- The script's text after the solver's header lines, from its shared assertions and definitions. -/
def Script.render (s : Script) (header : List String) (asserts : List Term) (defs : List (Term × Srt)) : String :=
  (s.parts header asserts defs).text

/-- The script's text after the solver's header lines; `none` as `Script.shared`. -/
def Script.text (s : Script) (header : List String) : Option String := do
  let (asserts, defs) ← s.shared
  pure (s.render header asserts defs)

/-- Whether the printer writes every term of the script as itself: every string lies in the SMT-LIB domain. -/
def Script.inDomain (s : Script) : Bool :=
  match s.shared with
  | some (asserts, defs) => asserts.all Term.inDomain && defs.all (·.1.inDomain)
  | none => false

inductive Answer where
  /-- Satisfiable, with the value of each variable asked for. -/
  | sat (values : List (Nat × Val))
  | unsat
  /-- No verdict: the solver said unknown (`solverUnknown`), which its resource limit decides the same way on every
  machine, or printed something else. -/
  | unknown (why : String)
  /-- No verdict: the solver ran past the wall-clock safety net, which depends on the machine. -/
  | timeout (ms : Nat)
deriving Repr

/-- Why an answer is unknown when the solver itself printed unknown. -/
def solverUnknown : String := "the solver answered unknown"

/-- Whether the answer is a function of the script's text and the solver's version alone: sat, unsat, or the solver's
own unknown, which its resource limit and seeds, set in the text's header, decide the same way on every machine. A
crash's output and a run past the wall clock depend on the machine. -/
def Answer.decided : Answer → Bool
  | .sat _ | .unsat => true
  | .unknown why => why == solverUnknown
  | .timeout _ => false

/-- Reads the solver's output. -/
def Answer.parse (text : String) : Answer :=
  match lex text with
  | some (.sym "unsat" :: _) => .unsat
  | some (.sym "unknown" :: _) => .unknown solverUnknown
  | some [.sym "sat"] => .sat []
  | some (.sym "sat" :: rest) =>
    let pair : SExp → Option (Nat × Val)
      | .list [.sym x, v] => match Name.read x.toList, Val.ofSExp v with
        | some (.var n), some val => some (n, val)
        | _, _ => none
      | _ => none
    match SExp.take rest with
    | some (.list pairs, _) => match pairs.mapM pair with
      | some vs => .sat vs
      | none => .unknown s!"the solver's values do not read: {text}"
    | _ => .unknown s!"the solver's values do not read: {text}"
  | _ => .unknown s!"the solver printed: {text.trimAscii}"

end Tazuna.Smt
