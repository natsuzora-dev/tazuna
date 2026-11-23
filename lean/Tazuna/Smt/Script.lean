import Std.Data.HashMap
import Tazuna.Smt.Date

/-!
The SMT-LIB script of a query, which TS hands to Z3 as text, and the reading of Z3's answer: `sat` with the values of
the declared variables, `unsat`, or `unknown`. Each term prints as the SMT-LIB operation that `Term.denote` gives it,
each compound term once as a definition.
-/

namespace Tazuna.Smt

def Ty.smt : Ty → String
  | .bool => "Bool"
  | .int => "Int"
  | .str => "String"
  | .val => "V"

/-- A symbol as SMT-LIB quotes it; names never hold `|` or a backslash. -/
def symbol (name : String) : String := "|" ++ name ++ "|"

def hexDigits (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- An SMT-LIB string literal: printable ASCII as is, `"` doubled, every other character as `\u{…}`. -/
def strLiteral (s : String) : String :=
  let esc (c : Char) : String :=
    if c == '"' then "\"\""
    else if c.toNat ≥ 0x20 && c.toNat ≤ 0x7E && c != '\\' then c.toString
    else "\\u{" ++ hexDigits c.toNat ++ "}"
  "\"" ++ String.join (s.toList.map esc) ++ "\""

def intLiteral (n : Int) : String := if n < 0 then s!"(- {n.natAbs})" else toString n

def Scalar.smt : Scalar → String
  | .undef => "vundef"
  | .null => "vnull"
  | .bool b => s!"(vbool {b})"
  | .int n => s!"(vint {intLiteral n})"
  | .str s => s!"(vstr {strLiteral s})"

def Lit.smt : Lit → String
  | .bool b => toString b
  | .int n => intLiteral n
  | .str s => strLiteral s
  | .val v => v.smt

/-- A compound term's SMT-LIB operator and its operands. -/
def Term.parts : Term → String × List Term
  | .var .. | .lit _ => ("", [])
  | .not a => ("not", [a])
  | .and a b => ("and", [a, b])
  | .or a b => ("or", [a, b])
  | .ite c a b => ("ite", [c, a, b])
  | .eq a b => ("=", [a, b])
  | .lt a b => ("<", [a, b])
  | .le a b => ("<=", [a, b])
  | .add a b => ("+", [a, b])
  | .sub a b => ("-", [a, b])
  | .mul a b => ("*", [a, b])
  | .div a b => ("div", [a, b])
  | .mod a b => ("mod", [a, b])
  | .len a => ("str.len", [a])
  | .prefixOf a b => ("str.prefixof", [a, b])
  | .suffixOf a b => ("str.suffixof", [a, b])
  | .contains a b => ("str.contains", [a, b])
  | .strAt a i => ("str.at", [a, i])
  | .toCode a => ("str.to_code", [a])
  | .fromCode a => ("str.from_code", [a])
  | .strCat a b => ("str.++", [a, b])
  | .dateLabel a => ("date_label", [a])
  | .mkBool a => ("vbool", [a])
  | .mkInt a => ("vint", [a])
  | .mkStr a => ("vstr", [a])
  | .isUndef a => ("(_ is vundef)", [a])
  | .isNull a => ("(_ is vnull)", [a])
  | .isBool a => ("(_ is vbool)", [a])
  | .isInt a => ("(_ is vint)", [a])
  | .isStr a => ("(_ is vstr)", [a])
  | .boolOf a => ("vbool_v", [a])
  | .intOf a => ("vint_v", [a])
  | .strOf a => ("vstr_v", [a])

/-- The sort of a term. -/
def Term.sort : Term → Ty
  | .var _ sort => sort
  | .lit (.bool _) => .bool
  | .lit (.int _) => .int
  | .lit (.str _) => .str
  | .lit (.val _) => .val
  | .ite _ a _ => a.sort
  | .add .. | .sub .. | .mul .. | .div .. | .mod .. | .len _ | .toCode _ | .intOf _ => .int
  | .strOf _ | .strAt .. | .fromCode _ | .strCat .. | .dateLabel _ => .str
  | .mkBool _ | .mkInt _ | .mkStr _ => .val
  | _ => .bool

/-- The definitions of the compound terms printed so far, each once, by its text with its operands named. -/
structure Shared where
  names : Std.HashMap String String := {}
  /-- Each definition's name, sort and text. -/
  defs : Array (String × Ty × String) := #[]
  /-- The name of each compound term printed so far, by its address in memory (Term.addr). -/
  printed : Std.HashMap USize String := {}

private unsafe def addrImpl (t : Term) : USize := ptrAddrUnsafe t

/--
Where `t` lives in memory. The encoding builds a term from subterms it holds once in memory and reads many times, so
printing walks each such subterm once by its address instead of once per occurrence. While a script is printed, the
query holds every term it reads, so no two of them share an address.
-/
@[implemented_by addrImpl] opaque Term.addr (t : Term) : USize

/--
`t` as SMT-LIB text: a variable or literal as itself, and a compound term as the name of a definition that is made once
for equal terms. The encoding repeats subterms, such as a record's field read in each condition that reads it, so
printing each occurrence in full made scripts of tens of megabytes.
-/
partial def Term.shared (t : Term) : StateM Shared String := do
  match t with
  | .var x _ => pure (symbol x)
  | .lit v => pure v.smt
  | _ =>
    if let some name := (← get).printed.get? t.addr then return name
    let (op, operands) := t.parts
    let names ← operands.mapM Term.shared
    let text := s!"({op} {" ".intercalate names})"
    let s ← get
    let name := (s.names.get? text).getD s!"|t{s.defs.size}|"
    let defs := if s.names.contains text then s.defs else s.defs.push (name, t.sort, text)
    set ({ names := s.names.insert text name, defs, printed := s.printed.insert t.addr name } : Shared)
    pure name

/-- A satisfiability question: its variables and the terms that must all hold. -/
structure Query where
  vars : List (String × Ty)
  asserts : List Term
deriving Inhabited

def datatypeV : String :=
  "(declare-datatypes ((V 0)) (((vundef) (vnull) (vbool (vbool_v Bool)) (vint (vint_v Int)) (vstr (vstr_v String)))))"

/-- The definition of `date_label` (Term.dateLabel) as dateLabelBody, its shared subterms bound by `let`. -/
def dateLabelDef : String :=
  let (text, shared) := (dateLabelBody (.var "z" .int)).shared.run {}
  let body := shared.defs.foldr (fun (name, _, bound) acc => s!"(let (({name} {bound})) {acc})") text
  s!"(define-fun date_label (({symbol "z"} Int)) String {body})"

/--
The script that asks Z3 whether `q` is satisfiable within `rlimit` units of Z3's resource counter, and for its model. A
resource limit instead of a time limit gives the same answer on a loaded machine as on an idle one. The query goes
straight to Z3's SMT core (the `smt` tactic): a plain check-sat first runs Z3's preprocessing, whose equation solving
substitutes each named variable back into the terms that name it, and spent most of a second on each two-order query of
a tie, ten times what the core took for the same answer.
-/
def Query.script (q : Query) (rlimit : Nat) : String :=
  let (asserted, shared) := (q.asserts.mapM Term.shared).run {}
  let lines := [s!"(set-option :rlimit {rlimit})", "(set-logic ALL)", datatypeV, dateLabelDef] ++
    q.vars.map (fun (x, t) => s!"(declare-const {symbol x} {t.smt})") ++
    shared.defs.toList.map (fun (name, sort, text) => s!"(define-fun {name} () {sort.smt} {text})") ++
    asserted.map (fun a => s!"(assert {a})") ++ ["(check-sat-using smt)"] ++
    (if q.vars.isEmpty then [] else [s!"(get-value ({" ".intercalate (q.vars.map (symbol ·.1))}))"])
  "\n".intercalate lines ++ "\n"

/-- An s-expression of Z3's output. -/
inductive Sexp where
  | atom (text : String)
  | str (value : String)
  | list (items : List Sexp)
deriving Inhabited

/-- The characters of a string literal up to its closing quote, unescaped, and the rest. -/
partial def readString (acc : List Char) : List Char → Option (String × List Char)
  | '"' :: '"' :: rest => readString ('"' :: acc) rest
  | '"' :: rest => some (String.ofList acc.reverse, rest)
  | '\\' :: 'u' :: '{' :: rest =>
    let digits := rest.takeWhile (· != '}')
    let n := digits.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0
    -- A surrogate is a character of SMT strings that no Lean string holds, so the model is no state.
    if n.isValidChar then readString (Char.ofNat n :: acc) (rest.drop (digits.length + 1)) else none
  | c :: rest => readString (c :: acc) rest
  | [] => none

mutual

partial def readSexp : List Char → Option (Sexp × List Char)
  | c :: rest =>
    if c.isWhitespace then readSexp rest
    else if c == '(' then readItems [] rest
    else if c == '"' then (readString [] rest).map fun (s, r) => (.str s, r)
    else if c == '|' then
      let name := rest.takeWhile (· != '|')
      some (.atom (String.ofList name), rest.drop (name.length + 1))
    else
      let text := (c :: rest).takeWhile fun d => !d.isWhitespace && d != '(' && d != ')'
      some (.atom (String.ofList text), rest.drop (text.length - 1))
  | [] => none

partial def readItems (acc : List Sexp) : List Char → Option (Sexp × List Char)
  | c :: rest =>
    if c.isWhitespace then readItems acc rest
    else if c == ')' then some (.list acc.reverse, rest)
    else match readSexp (c :: rest) with
      | some (s, r) => readItems (s :: acc) r
      | none => none
  | [] => none

end

def Sexp.int? : Sexp → Option Int
  | .atom t => t.toNat?.map Int.ofNat
  | .list [.atom "-", .atom t] => t.toNat?.map fun n => -Int.ofNat n
  | _ => none

def Sexp.lit? : Sexp → Option Lit
  | .atom "true" => some (.bool true)
  | .atom "false" => some (.bool false)
  | .atom "vundef" => some (.val .undef)
  | .atom "vnull" => some (.val .null)
  | .str s => some (.str s)
  | .list [.atom "vbool", .atom b] => some (.val (.bool (b == "true")))
  | .list [.atom "vint", n] => n.int?.map fun n => .val (.int n)
  | .list [.atom "vstr", .str s] => some (.val (.str s))
  | s => s.int?.map .int

/-- Z3's answer to a query. -/
inductive Answer where
  | sat (values : List (String × Lit))
  | unsat
  | unknown (reason : String)
deriving Inhabited

/-- The answer that Z3's output `text` gives: its first line, and with `sat` the values that get-value printed. -/
def Answer.read (text : String) : Answer :=
  let chars := text.toList.dropWhile Char.isWhitespace
  let first := String.ofList (chars.takeWhile (!·.isWhitespace))
  match first with
  | "unsat" => .unsat
  | "sat" =>
    match readSexp (chars.drop 3) with
    | some (.list pairs, _) =>
      let values := pairs.filterMap fun
        | .list [.atom name, v] => v.lit?.map (name, ·)
        | _ => none
      if values.length == pairs.length then .sat values else .unknown s!"unreadable model: {text}"
    | _ => .unknown "the solver's model holds a character that no Lean string holds, a surrogate"
  | "unknown" => .unknown "the solver answered unknown, as at its resource limit"
  | _ => .unknown s!"unreadable answer: {text}"

def Answer.model (values : List (String × Lit)) : Model := fun x => (values.lookup x).getD (.val .undef)

end Tazuna.Smt
