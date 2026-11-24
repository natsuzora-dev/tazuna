import Tazuna.Smt.Syntax

/-! A script is one question to the solver in standard SMT-LIB 2.6: declarations, assertions, a plain `(check-sat)`
and, for a sat answer, the values of the variables it asks for. The answer names each value by its variable, so a
caller reads values by name, never by position. -/

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

structure Script where
  /-- Datatype `i` may refer only to datatypes before it. -/
  datatypes : List Datatype := []
  /-- The sort of each variable `v<n>`, by `n`. -/
  vars : List Srt := []
  asserts : List Term := []
  /-- The variables whose values a sat answer reports. -/
  shows : List Nat := []

/-- The script's text after the solver's header lines. -/
def Script.text (s : Script) (header : List String) : String :=
  let lines := header ++ ["(set-option :produce-models true)", "(set-logic ALL)"] ++
    s.datatypes.zipIdx.map (fun (d, i) => d.text i) ++
    s.vars.zipIdx.map (fun (srt, n) => s!"(declare-const {(Name.var n).text} {srt.text})") ++
    s.asserts.map (fun t => s!"(assert {t.print})") ++ ["(check-sat)"] ++
    (if s.shows.isEmpty then [] else
      [s!"(get-value ({" ".intercalate (s.shows.map fun n => (Name.var n).text)}))"])
  "\n".intercalate lines ++ "\n"

/-- Whether every string the script writes lies in the SMT-LIB domain, so the printer writes it as itself. -/
def Script.inDomain (s : Script) : Bool := s.asserts.all Term.inDomain

inductive Answer where
  /-- Satisfiable, with the value of each variable asked for. -/
  | sat (values : List (Nat × Val))
  | unsat
  /-- No verdict: the solver said unknown, ran out of time or resources, or printed something else. -/
  | unknown (why : String)
deriving Repr

def Answer.value? : Answer → Nat → Option Val
  | .sat vs, n => vs.lookup n
  | _, _ => none

/-- Reads the solver's output. -/
def Answer.parse (text : String) : Answer :=
  match lex text with
  | some (.sym "unsat" :: _) => .unsat
  | some (.sym "unknown" :: _) => .unknown "the solver answered unknown"
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
