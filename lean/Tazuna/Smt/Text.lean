import Tazuna.Ir.Literal
import Tazuna.Smt.Term

/-! SMT-LIB text as S-expressions: printing, and reading back what a solver prints. The printer writes a list's items
one space apart inside its parentheses, as solvers print; the reader takes any whitespace, so it reads any layout.
`SExp.parse_print` proves that reading a printed S-expression gives it back. -/

namespace Tazuna.Smt

open Tazuna.Ir.Literal (decimalDigits digitChar hexValue)

inductive Token where
  | lp
  | rp
  | sym (s : String)
  | num (n : Nat)
  | str (s : String)
deriving DecidableEq, Repr

inductive SExp where
  | sym (s : String)
  | num (n : Nat)
  | str (s : String)
  | list (xs : List SExp)
deriving Repr, Inhabited

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- The characters of SMT-LIB's simple symbols. -/
def isSymChar (c : Char) : Bool := c.isAlphanum || "~!@$%^&*_-+=<>.?/".toList.contains c

def isSpace (c : Char) : Bool := c = ' ' || c = '\n' || c = '\t' || c = '\r'

def hexChar (d : Nat) : Char := Char.ofNat (if d < 10 then 48 + d else 87 + d)

def hex5 (n : Nat) : List Char := [n / 65536 % 16, n / 4096 % 16, n / 256 % 16, n / 16 % 16, n % 16].map hexChar

/-- How a string literal writes a character: printable ASCII as itself with `"` doubled, every other character as
`\u{XXXXX}`, which covers the string domain up to U+2FFFF. -/
def escape (c : Char) : List Char :=
  if c = '"' then ['"', '"']
  else if 32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '\\' then [c]
  else ['\\', 'u', '{'] ++ hex5 c.toNat ++ ['}']

def Token.chars : Token → List Char
  | .lp => ['(']
  | .rp => [')']
  | .sym s => s.toList
  | .num n => (decimalDigits n).map digitChar
  | .str s => '"' :: s.toList.flatMap escape ++ ['"']

mutual
def SExp.tokens : SExp → List Token
  | .sym s => [.sym s]
  | .num n => [.num n]
  | .str s => [.str s]
  | .list xs => .lp :: SExp.tokensList xs ++ [.rp]
def SExp.tokensList : List SExp → List Token
  | [] => []
  | x :: xs => SExp.tokens x ++ SExp.tokensList xs
end

mutual
/-- The text of an S-expression as SMT-LIB solvers print one: a list's items one space apart inside its parentheses,
as in `(f x (g y))`. -/
def SExp.layout : SExp → List Char
  | .sym s => (Token.sym s).chars
  | .num n => (Token.num n).chars
  | .str s => (Token.str s).chars
  | .list xs => '(' :: SExp.layoutList xs ++ [')']
def SExp.layoutList : List SExp → List Char
  | [] => []
  | x :: xs => SExp.layout x ++ SExp.layoutRest xs
/-- Items after the first, each after a space. -/
def SExp.layoutRest : List SExp → List Char
  | [] => []
  | x :: xs => ' ' :: SExp.layout x ++ SExp.layoutRest xs
end

def SExp.print (e : SExp) : String := String.ofList e.layout

mutual
/-- `SExp.print` after the text `acc`, appended in place: the compiled printer, since a script's text built as a list
of characters took most of the time a cache hit spends. -/
def SExp.write (acc : String) : SExp → String
  | .sym s => acc ++ s
  | .num n => acc ++ String.ofList (Token.num n).chars
  | .str s => acc ++ String.ofList (Token.str s).chars
  | .list xs => (SExp.writeList (acc.push '(') xs).push ')'
def SExp.writeList (acc : String) : List SExp → String
  | [] => acc
  | x :: xs => SExp.writeRest (SExp.write acc x) xs
def SExp.writeRest (acc : String) : List SExp → String
  | [] => acc
  | x :: xs => SExp.writeRest (SExp.write (acc.push ' ') x) xs
end

def SExp.printFast (e : SExp) : String := SExp.write "" e

mutual
theorem SExp.write_eq (acc : String) : (e : SExp) → SExp.write acc e = acc ++ String.ofList e.layout
  | .sym s => by simp [SExp.write, SExp.layout, Token.chars]
  | .num n => by simp [SExp.write, SExp.layout]
  | .str s => by simp only [SExp.write, SExp.layout]
  | .list xs => by
    rw [SExp.write, SExp.writeList_eq]
    simp [SExp.layout, String.push_eq_append, String.ofList_append, String.append_assoc, String.ofList_cons]
theorem SExp.writeList_eq (acc : String) : (xs : List SExp) →
    SExp.writeList acc xs = acc ++ String.ofList (SExp.layoutList xs)
  | [] => by simp [SExp.writeList, SExp.layoutList]
  | x :: xs => by
    rw [SExp.writeList, SExp.writeRest_eq, SExp.write_eq, SExp.layoutList, String.ofList_append, String.append_assoc]
theorem SExp.writeRest_eq (acc : String) : (xs : List SExp) →
    SExp.writeRest acc xs = acc ++ String.ofList (SExp.layoutRest xs)
  | [] => by simp [SExp.writeRest, SExp.layoutRest]
  | x :: xs => by
    rw [SExp.writeRest, SExp.writeRest_eq, SExp.write_eq, SExp.layoutRest]
    simp [String.push_eq_append, String.ofList_append, String.append_assoc, String.ofList_cons]
end

@[csimp] theorem SExp.print_eq_printFast : @SExp.print = @SExp.printFast := by
  funext e
  simp [SExp.print, SExp.printFast, SExp.write_eq]

/-! Reading. -/

/-- Where the reader is inside a string literal's escapes. A backslash that starts no `\u{...}` escape stands for
itself, as SMT-LIB 2.6 says, so `raw` keeps what an escape in progress has read. -/
inductive Dec where
  | plain
  | backslash
  | u
  | hex (value count : Nat) (raw : List Char)
deriving DecidableEq

def plainStep (c : Char) : Dec × List Char := if c = '\\' then (.backslash, []) else (.plain, [c])

def decStep : Dec → Char → Dec × List Char
  | .plain, c => plainStep c
  | .backslash, c => if c = 'u' then (.u, []) else let (st, out) := plainStep c; (st, '\\' :: out)
  | .u, c => if c = '{' then (.hex 0 0 [], []) else let (st, out) := plainStep c; (st, ['\\', 'u'] ++ out)
  | .hex v k raw, c =>
    let unread := let (st, out) := plainStep c; (st, ['\\', 'u', '{'] ++ raw ++ out)
    if c = '}' then (if 0 < k then (.plain, [Char.ofNat v]) else unread)
    else match hexValue c with
      | some d => if k < 5 then (.hex (v * 16 + d) (k + 1) (raw ++ [c]), []) else unread
      | none => unread

def decodeFrom : Dec → List Char → List Char
  | .plain, [] => []
  | .backslash, [] => ['\\']
  | .u, [] => ['\\', 'u']
  | .hex _ _ raw, [] => ['\\', 'u', '{'] ++ raw
  | st, c :: cs => let (st', out) := decStep st c; out ++ decodeFrom st' cs

/-- Where the lexer is: between tokens, inside a symbol, a numeral or a string literal, or just after a `"` inside a
string literal, which either doubles the quote or ends the literal. -/
inductive Lex where
  | idle
  | sym (acc : List Char)
  | num (n : Nat)
  | str (acc : List Char)
  | quote (acc : List Char)
deriving DecidableEq

def idleStep (c : Char) : Option (Lex × List Token) :=
  if isSpace c then some (.idle, [])
  else if c = '(' then some (.idle, [.lp])
  else if c = ')' then some (.idle, [.rp])
  else if c = '"' then some (.str [], [])
  else if isDigit c then some (.num (c.toNat - 48), [])
  else if isSymChar c then some (.sym [c], [])
  else none

def strToken (acc : List Char) : Option Token := some (.str (String.ofList (decodeFrom .plain acc)))

def lexStep : Lex → Char → Option (Lex × List Token)
  | .idle, c => idleStep c
  | .sym acc, c =>
    if isSymChar c then some (.sym (acc ++ [c]), [])
    else (idleStep c).map fun (st, ts) => (st, .sym (String.ofList acc) :: ts)
  | .num n, c =>
    if isDigit c then some (.num (n * 10 + (c.toNat - 48)), [])
    else (idleStep c).map fun (st, ts) => (st, .num n :: ts)
  | .str acc, c => if c = '"' then some (.quote acc, []) else some (.str (acc ++ [c]), [])
  | .quote acc, c =>
    if c = '"' then some (.str (acc ++ ['"']), [])
    else do
      let t ← strToken acc
      let (st, ts) ← idleStep c
      pure (st, t :: ts)

def lexFrom : Lex → List Char → Option (List Token)
  | .idle, [] => some []
  | .sym acc, [] => some [.sym (String.ofList acc)]
  | .num n, [] => some [.num n]
  | .str _, [] => none
  | .quote acc, [] => (strToken acc).map ([·])
  | st, c :: cs => do
    let (st', ts) ← lexStep st c
    let rest ← lexFrom st' cs
    pure (ts ++ rest)

def lex (s : String) : Option (List Token) := lexFrom .idle s.toList

mutual
/-- One S-expression from the front of the tokens; `fuel` bounds the nesting. -/
def parseExp : Nat → List Token → Option (SExp × List Token)
  | 0, _ => none
  | _ + 1, .sym s :: r => some (.sym s, r)
  | _ + 1, .num n :: r => some (.num n, r)
  | _ + 1, .str s :: r => some (.str s, r)
  | n + 1, .lp :: r => (parseItems n r).map fun (xs, r) => (.list xs, r)
  | _ + 1, _ => none
/-- The items of a list up to its `)`. -/
def parseItems : Nat → List Token → Option (List SExp × List Token)
  | 0, _ => none
  | _ + 1, .rp :: r => some ([], r)
  | n + 1, ts => do
    let (x, r) ← parseExp n ts
    let (xs, r) ← parseItems n r
    pure (x :: xs, r)
end

/-- One S-expression from the front of the tokens, with the tokens after it. -/
def SExp.take (ts : List Token) : Option (SExp × List Token) := parseExp (ts.length + 1) ts

def SExp.parse (text : String) : Option SExp := do
  let (e, rest) ← SExp.take (← lex text)
  if rest.isEmpty then some e else none

/-! Reading back what was printed. -/

/-- A token the printer writes as itself: a symbol is simple and starts with no digit, and a string stays in the SMT-LIB
string domain. -/
def Token.wf : Token → Prop
  | .sym s => ∃ c cs, s.toList = c :: cs ∧ isDigit c = false ∧ isSymChar c = true ∧ ∀ x ∈ cs, isSymChar x = true
  | .str s => ∀ c ∈ s.toList, c.toNat ≤ maxChar
  | _ => True

theorem hexChar_facts : ∀ d : Fin 16, hexValue (hexChar d) = some d.val ∧ hexChar d ≠ '}' ∧ hexChar d ≠ '"' := by
  decide

theorem hexValue_hexChar (d : Nat) (h : d < 16) : hexValue (hexChar d) = some d := (hexChar_facts ⟨d, h⟩).1

theorem hexChar_ne_brace (d : Nat) (h : d < 16) : hexChar d ≠ '}' := (hexChar_facts ⟨d, h⟩).2.1

theorem hexChar_ne_quote (d : Nat) (h : d < 16) : hexChar d ≠ '"' := (hexChar_facts ⟨d, h⟩).2.2

/-- What the lexer keeps of an escaped character: the doubled quote reads as one. -/
def unquoted (c : Char) : List Char := if c = '"' then ['"'] else escape c

theorem decodeFrom_hex (v k : Nat) (raw : List Char) (ds : List Nat) (hds : ∀ d ∈ ds, d < 16)
    (hk : k + ds.length ≤ 5) (r : List Char) :
    decodeFrom (.hex v k raw) (ds.map hexChar ++ r) =
      decodeFrom (.hex (ds.foldl (fun a d => a * 16 + d) v) (k + ds.length) (raw ++ ds.map hexChar)) r := by
  induction ds generalizing v k raw with
  | nil => simp
  | cons d ds ih =>
    have hd := hds d (by simp)
    simp only [List.map_cons, List.cons_append, decodeFrom, decStep, hexChar_ne_brace d hd, ite_false,
      hexValue_hexChar d hd]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp at hk; omega))]
    simp only [List.nil_append, List.foldl_cons]
    rw [ih (v * 16 + d) (k + 1) _ (fun x hx => hds x (by simp [hx])) (by simp at hk; omega)]
    have : k + 1 + ds.length = k + (ds.length + 1) := by omega
    rw [this]
    simp

theorem decode_unquoted (c : Char) (hc : c.toNat ≤ maxChar) (r : List Char) :
    decodeFrom .plain (unquoted c ++ r) = c :: decodeFrom .plain r := by
  unfold unquoted escape
  by_cases hq : c = '"'
  · subst hq; simp [decodeFrom, decStep, plainStep]
  simp only [hq, ite_false]
  by_cases hp : 32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c ≠ '\\'
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hp)]
    simp [decodeFrom, decStep, plainStep, hp.2.2]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hp)]
    have hlt : ∀ d ∈ [c.toNat / 65536 % 16, c.toNat / 4096 % 16, c.toNat / 256 % 16, c.toNat / 16 % 16, c.toNat % 16],
        d < 16 := by intro d hd; simp at hd; omega
    simp only [List.cons_append, List.nil_append, List.append_assoc, decodeFrom, decStep, plainStep, ite_true]
    rw [hex5, decodeFrom_hex 0 0 [] _ hlt (by simp)]
    simp only [List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil, decodeFrom, decStep, ite_true]
    have hv : ((((0 * 16 + c.toNat / 65536 % 16) * 16 + c.toNat / 4096 % 16) * 16 + c.toNat / 256 % 16) * 16 +
        c.toNat / 16 % 16) * 16 + c.toNat % 16 = c.toNat := by unfold maxChar at hc; omega
    simp only [hv, show (0 : Nat) < 0 + 1 + 1 + 1 + 1 + 1 from by decide, ite_true, Char.ofNat_toNat,
      List.singleton_append, List.nil_append]

theorem decode_unquoteds (cs : List Char) (hcs : ∀ c ∈ cs, c.toNat ≤ maxChar) :
    decodeFrom .plain (cs.flatMap unquoted) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, decode_unquoted c (hcs c (by simp)), ih (fun x hx => hcs x (by simp [hx]))]

theorem escape_no_quote (c : Char) (hq : c ≠ '"') : '"' ∉ escape c := by
  unfold escape
  simp only [hq, ite_false]
  split
  · simp; exact fun h => hq h.symm
  · simp only [hex5, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    have h16 : ∀ n : Nat, n % 16 < 16 := fun n => Nat.mod_lt _ (by decide)
    intro h
    rcases h with h | h | h | h | h | h | h | h | h
    all_goals first
      | exact absurd h (by decide)
      | exact hexChar_ne_quote _ (h16 _) h.symm

theorem lex_str_plain (ds acc tail : List Char) (hd : '"' ∉ ds) :
    lexFrom (.str acc) (ds ++ tail) = lexFrom (.str (acc ++ ds)) tail := by
  induction ds generalizing acc with
  | nil => simp
  | cons d ds ihd =>
    have hd' : d ≠ '"' := fun e => hd (e ▸ by simp)
    simp only [List.cons_append, lexFrom, lexStep, hd', ite_false, Option.bind_eq_bind, Option.bind_some]
    rw [ihd (acc ++ [d]) (fun h => hd (by simp [h]))]
    simp

theorem lex_str_body (acc cs : List Char) (r : List Char) :
    lexFrom (.str acc) (cs.flatMap escape ++ r) = lexFrom (.str (acc ++ cs.flatMap unquoted)) r := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.flatMap_cons, List.append_assoc]
    by_cases hq : c = '"'
    · subst hq
      simp only [escape, ite_true, List.cons_append, List.nil_append, lexFrom, lexStep, ite_true,
        Option.bind_eq_bind, Option.bind_some]
      rw [ih]
      simp [unquoted]
    · rw [lex_str_plain (escape c) acc _ (escape_no_quote c hq), ih]
      simp [unquoted, hq]

theorem digitChar_facts : ∀ d : Fin 10, isDigit (digitChar d) = true ∧ (digitChar d).toNat - 48 = d.val := by
  decide

theorem idle_space : idleStep ' ' = some (.idle, []) := by decide
theorem idle_lp : idleStep '(' = some (.idle, [.lp]) := by decide
theorem idle_rp : idleStep ')' = some (.idle, [.rp]) := by decide
theorem idle_quote : idleStep '"' = some (.str [], []) := by decide

theorem idle_sym (c : Char) (hdig : isDigit c = false) (hsym : isSymChar c = true) :
    idleStep c = some (.sym [c], []) := by
  have hsp : isSpace c = false := by
    cases hc : isSpace c
    · rfl
    · simp only [isSpace, Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with ((h | h) | h) | h <;> subst h <;> exact absurd hsym (by decide)
  have hl : c ≠ '(' := by intro e; subst e; exact absurd hsym (by decide)
  have hr : c ≠ ')' := by intro e; subst e; exact absurd hsym (by decide)
  have hq : c ≠ '"' := by intro e; subst e; exact absurd hsym (by decide)
  simp [idleStep, hsp, hl, hr, hq, hdig, hsym]

theorem idle_digit (d : Nat) (h : d < 10) : idleStep (digitChar d) = some (.num d, []) := by
  have := (⟨d, h⟩ : Fin 10).isLt
  have key : ∀ e : Fin 10, idleStep (digitChar e) = some (.num e.val, []) := by decide
  exact key ⟨d, h⟩

theorem lexFrom_cons {st st' : Lex} {c : Char} {ts : List Token} (cs : List Char) (h : lexStep st c = some (st', ts)) :
    lexFrom st (c :: cs) = (lexFrom st' cs).map (ts ++ ·) := by
  cases st <;> simp only [lexFrom, h, Option.bind_eq_bind, Option.bind_some] <;> cases lexFrom st' cs <;> rfl

theorem lexFrom_idle {st' : Lex} {c : Char} {ts : List Token} (cs : List Char) (h : idleStep c = some (st', ts)) :
    lexFrom .idle (c :: cs) = (lexFrom st' cs).map (ts ++ ·) := lexFrom_cons (st := .idle) cs h

/-- What the printer writes after an S-expression: nothing, the space before the next item, or the `)` of its list. -/
def Gap (rest : List Char) : Prop := ∀ c r, rest = c :: r → c = ' ' ∨ c = ')'

/-- At a gap, the lexer emits the token it holds in state `st` and goes on idle. -/
theorem lex_pending (st : Lex) (tok : Token)
    (hst : ∀ c, (c = ' ' ∨ c = ')') → lexStep st c = (idleStep c).map fun (s, ts) => (s, tok :: ts))
    (hend : lexFrom st [] = some [tok]) (rest : List Char) (hg : Gap rest) :
    lexFrom st rest = (lexFrom .idle rest).map (tok :: ·) := by
  cases rest with
  | nil => simp [hend, lexFrom]
  | cons c r =>
    rcases hg c r rfl with rfl | rfl
    · rw [lexFrom_cons r (by rw [hst ' ' (.inl rfl), idle_space]; rfl), lexFrom_idle r idle_space]
      cases lexFrom .idle r <;> rfl
    · rw [lexFrom_cons r (by rw [hst ')' (.inr rfl), idle_rp]; rfl), lexFrom_idle r idle_rp]
      cases lexFrom .idle r <;> rfl

theorem lex_sym_chars (acc cs rest : List Char) (h : ∀ x ∈ cs, isSymChar x = true) :
    lexFrom (.sym acc) (cs ++ rest) = lexFrom (.sym (acc ++ cs)) rest := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.cons_append, lexFrom_cons (st' := .sym (acc ++ [c])) (ts := []) _ (by simp [lexStep, h c (by simp)]),
      ih (acc ++ [c]) (fun x hx => h x (by simp [hx]))]
    simp

theorem lex_num_chars (acc : Nat) (ds : List Nat) (rest : List Char) (h : ∀ d ∈ ds, d < 10) :
    lexFrom (.num acc) (ds.map digitChar ++ rest) = lexFrom (.num (ds.foldl (fun a d => a * 10 + d) acc)) rest := by
  induction ds generalizing acc with
  | nil => simp
  | cons d ds ih =>
    have hd := digitChar_facts ⟨d, h d (by simp)⟩
    rw [List.map_cons, List.cons_append,
      lexFrom_cons (st' := .num (acc * 10 + d)) (ts := []) _ (by simp [lexStep, hd.1, hd.2]),
      ih _ (fun x hx => h x (by simp [hx]))]
    simp

theorem lex_atom (t : Token) (ht : t.wf) (hl : t ≠ .lp) (hr : t ≠ .rp) (rest : List Char) (hg : Gap rest) :
    lexFrom .idle (t.chars ++ rest) = (lexFrom .idle rest).map (t :: ·) := by
  cases t with
  | lp => exact absurd rfl hl
  | rp => exact absurd rfl hr
  | sym s =>
    obtain ⟨c, cs, hs, hdig, hsym, hcs⟩ := ht
    rw [Token.chars, hs, List.cons_append, lexFrom_idle _ (idle_sym c hdig hsym), lex_sym_chars [c] cs rest hcs,
      lex_pending _ (.sym s) (fun x hx => by
        rcases hx with rfl | rfl <;> simp [lexStep, isSymChar, ← hs, String.ofList_toList])
        (by simp [lexFrom, ← hs, String.ofList_toList]) rest hg]
    simp [Option.map_map, Function.comp_def]
  | num n =>
    have hlt := Tazuna.Ir.Literal.decimalDigits_lt n
    have hfold := Tazuna.Ir.Literal.foldl_decimalDigits n
    cases hds : decimalDigits n with
    | nil => rw [Tazuna.Ir.Literal.decimalDigits] at hds; split at hds <;> simp at hds
    | cons d ds =>
      rw [hds] at hlt hfold
      simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add] at hfold
      rw [Token.chars, hds, List.map_cons, List.cons_append, lexFrom_idle _ (idle_digit d (hlt d (by simp))),
        lex_num_chars d ds rest (fun x hx => hlt x (by simp [hx])), hfold,
        lex_pending _ (.num n) (fun x hx => by rcases hx with rfl | rfl <;> simp [lexStep, isDigit])
          (by simp [lexFrom]) rest hg]
      simp [Option.map_map, Function.comp_def]
  | str s =>
    rw [Token.chars, List.append_assoc, List.cons_append, lexFrom_idle _ idle_quote, lex_str_body [] s.toList _,
      List.singleton_append,
      lexFrom_cons (st' := .quote ([] ++ s.toList.flatMap unquoted)) (ts := []) _ (by simp [lexStep]),
      lex_pending _ (.str s) (fun x hx => by
        rcases hx with rfl | rfl <;> simp [lexStep, strToken, decode_unquoteds s.toList ht, idle_space, idle_rp])
        (by simp [lexFrom, strToken, decode_unquoteds s.toList ht]) rest hg]
    simp [Option.map_map, Function.comp_def]

theorem gap_layoutRest (xs : List SExp) (rest : List Char) (hg : Gap rest) : Gap (SExp.layoutRest xs ++ rest) := by
  cases xs with
  | nil => simpa [SExp.layoutRest] using hg
  | cons y ys => intro c r e; simp only [SExp.layoutRest, List.cons_append, List.cons.injEq] at e; exact .inl e.1.symm

mutual
theorem lex_layout : (e : SExp) → (∀ t ∈ e.tokens, t.wf) → (rest : List Char) → Gap rest →
    lexFrom .idle (e.layout ++ rest) = (lexFrom .idle rest).map (e.tokens ++ ·)
  | .sym s, h, rest, hg => by
    simpa [SExp.layout, SExp.tokens] using lex_atom (.sym s) (h _ (by simp [SExp.tokens])) nofun nofun rest hg
  | .num n, h, rest, hg => by
    simpa [SExp.layout, SExp.tokens] using lex_atom (.num n) (h _ (by simp [SExp.tokens])) nofun nofun rest hg
  | .str s, h, rest, hg => by
    simpa [SExp.layout, SExp.tokens] using lex_atom (.str s) (h _ (by simp [SExp.tokens])) nofun nofun rest hg
  | .list xs, h, rest, hg => by
    have hxs : ∀ t ∈ SExp.tokensList xs, t.wf := fun t ht => h t (by simp [SExp.tokens, ht])
    rw [SExp.layout, List.append_assoc, List.cons_append, List.singleton_append, lexFrom_idle _ idle_lp,
      lex_layoutList xs hxs (')' :: rest) (fun c r e => by cases e; exact .inr rfl), lexFrom_idle _ idle_rp]
    simp [SExp.tokens, Option.map_map, Function.comp_def]
theorem lex_layoutList : (xs : List SExp) → (∀ t ∈ SExp.tokensList xs, t.wf) → (rest : List Char) → Gap rest →
    lexFrom .idle (SExp.layoutList xs ++ rest) = (lexFrom .idle rest).map (SExp.tokensList xs ++ ·)
  | [], _, rest, _ => by simp [SExp.layoutList, SExp.tokensList]
  | x :: xs, h, rest, hg => by
    have hx : ∀ t ∈ x.tokens, t.wf := fun t ht => h t (by simp [SExp.tokensList, ht])
    have hxs : ∀ t ∈ SExp.tokensList xs, t.wf := fun t ht => h t (by simp [SExp.tokensList, ht])
    rw [SExp.layoutList, List.append_assoc, lex_layout x hx _ (gap_layoutRest xs rest hg),
      lex_layoutRest xs hxs rest hg]
    simp [SExp.tokensList, Option.map_map, Function.comp_def]
theorem lex_layoutRest : (xs : List SExp) → (∀ t ∈ SExp.tokensList xs, t.wf) → (rest : List Char) → Gap rest →
    lexFrom .idle (SExp.layoutRest xs ++ rest) = (lexFrom .idle rest).map (SExp.tokensList xs ++ ·)
  | [], _, rest, _ => by simp [SExp.layoutRest, SExp.tokensList]
  | x :: xs, h, rest, hg => by
    have hx : ∀ t ∈ x.tokens, t.wf := fun t ht => h t (by simp [SExp.tokensList, ht])
    have hxs : ∀ t ∈ SExp.tokensList xs, t.wf := fun t ht => h t (by simp [SExp.tokensList, ht])
    rw [SExp.layoutRest, List.append_assoc, List.cons_append, lexFrom_idle _ idle_space,
      lex_layout x hx _ (gap_layoutRest xs rest hg), lex_layoutRest xs hxs rest hg]
    simp [SExp.tokensList, Option.map_map, Function.comp_def]
end

mutual
theorem SExp.tokens_ne : (e : SExp) → ∃ t ts, e.tokens = t :: ts ∧ t ≠ .rp
  | .sym _ => ⟨_, _, rfl, by simp⟩
  | .num _ => ⟨_, _, rfl, by simp⟩
  | .str _ => ⟨_, _, rfl, by simp⟩
  | .list _ => ⟨_, _, rfl, by simp⟩
end

theorem SExp.tokens_length_pos (e : SExp) : 1 ≤ e.tokens.length := by
  obtain ⟨t, ts, h, _⟩ := e.tokens_ne; rw [h]; simp

theorem parseItems_cons (n : Nat) (t : Token) (ts : List Token) (h : t ≠ .rp) :
    parseItems (n + 1) (t :: ts) = (do
      let (x, r) ← parseExp n (t :: ts)
      let (xs, r) ← parseItems n r
      pure (x :: xs, r)) := by
  cases t <;> first | exact absurd rfl h | rfl

mutual
theorem parseExp_tokens : (e : SExp) → (n : Nat) → e.tokens.length < n → (r : List Token) →
    parseExp n (e.tokens ++ r) = some (e, r)
  | .sym _, n + 1, _, _ => rfl
  | .num _, n + 1, _, _ => rfl
  | .str _, n + 1, _, _ => rfl
  | .list xs, n + 1, h, r => by
    simp only [SExp.tokens, List.length_cons, List.length_append] at h
    simp only [SExp.tokens, List.cons_append, List.append_assoc, List.nil_append, parseExp]
    rw [parseItems_tokens xs n (by omega) r]
    rfl
  | .sym _, 0, h, _ | .num _, 0, h, _ | .str _, 0, h, _ | .list _, 0, h, _ => by simp at h
theorem parseItems_tokens : (xs : List SExp) → (n : Nat) → (SExp.tokensList xs).length + 1 < n →
    (r : List Token) → parseItems n (SExp.tokensList xs ++ .rp :: r) = some (xs, r)
  | [], n + 1, _, _ => rfl
  | x :: xs, n + 1, h, r => by
    have hpos := x.tokens_length_pos
    simp only [SExp.tokensList, List.length_append] at h
    obtain ⟨t, ts, ht, hne⟩ := x.tokens_ne
    have hx := parseExp_tokens x n (by omega) (SExp.tokensList xs ++ .rp :: r)
    have hxs := parseItems_tokens xs n (by omega) r
    simp only [SExp.tokensList, List.append_assoc]
    rw [ht] at hx ⊢
    rw [List.cons_append, parseItems_cons n t _ hne, ← List.cons_append, hx]
    simp only [Option.bind_eq_bind, Option.bind_some, hxs, Option.pure_def]
  | [], 0, h, _ | _ :: _, 0, h, _ => by simp at h
end

/-- An S-expression the printer writes as itself: each of its tokens is. -/
def SExp.wf (e : SExp) : Prop := ∀ t ∈ e.tokens, t.wf

/-- Reading back a printed S-expression gives it. -/
theorem SExp.parse_print (e : SExp) (h : e.wf) : SExp.parse e.print = some e := by
  have hl : lex e.print = some e.tokens := by
    simpa [lex, SExp.print, lexFrom] using lex_layout e h [] (fun _ _ e => nomatch e)
  simp only [SExp.parse, hl, Option.bind_eq_bind, Option.bind_some, SExp.take]
  have := parseExp_tokens e (e.tokens.length + 1) (by omega) []
  rw [List.append_nil] at this
  rw [this]
  rfl

end Tazuna.Smt
