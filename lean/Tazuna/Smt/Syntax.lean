import Tazuna.Smt.Text

/-! Terms and values as S-expressions. Names are generated so that reading them back needs no table: variable `n` is
`v<n>`, constructor `k` of datatype `d` is `D<d>_<k>`, its field `j` is `D<d>_<k>_<j>`, and a script's definition `i`
is `s<i>`. `Term.ofSExp_toSExp` and
`Term.parse_print` prove that reading a printed term gives it back; values are terms without variables or
operations, so the same holds for them (`Val.parse_print`). -/

namespace Tazuna.Smt

open Tazuna.Ir.Literal (decimalDigits digitChar)

def decChars (n : Nat) : List Char := (decimalDigits n).map digitChar

def readDigits (acc : Nat) : List Char → Nat × List Char
  | c :: cs => if isDigit c then readDigits (acc * 10 + (c.toNat - 48)) cs else (acc, c :: cs)
  | [] => (acc, [])

/-- The decimal numeral at the front, with what follows it. -/
def readNat : List Char → Option (Nat × List Char)
  | c :: cs => if isDigit c then some (readDigits (c.toNat - 48) cs) else none
  | [] => none

inductive Name where
  | var (n : Nat)
  | ctor (d k : Nat)
  | sel (d k j : Nat)
  | def_ (i : Nat)
deriving DecidableEq, Repr

def Name.chars : Name → List Char
  | .var n => 'v' :: decChars n
  | .ctor d k => 'D' :: decChars d ++ '_' :: decChars k
  | .sel d k j => 'D' :: decChars d ++ '_' :: decChars k ++ '_' :: decChars j
  | .def_ i => 's' :: decChars i

def Name.text (n : Name) : String := String.ofList n.chars

def Name.read : List Char → Option Name
  | 'v' :: cs => match readNat cs with
    | some (n, []) => some (.var n)
    | _ => none
  | 's' :: cs => match readNat cs with
    | some (i, []) => some (.def_ i)
    | _ => none
  | 'D' :: cs => match readNat cs with
    | some (d, '_' :: cs) => match readNat cs with
      | some (k, []) => some (.ctor d k)
      | some (k, '_' :: cs) => match readNat cs with
        | some (j, []) => some (.sel d k j)
        | _ => none
      | _ => none
    | _ => none
  | _ => none

inductive Op1 where
  | not | len
deriving DecidableEq, Repr

inductive Op2 where
  | and | or | eq | lt | le | add | sub | mul | div | mod | cat | slt
deriving DecidableEq, Repr

/-- What a symbol stands for. -/
inductive Sym where
  | op1 (o : Op1)
  | op2 (o : Op2)
  | ite
  | lit (b : Bool)
  | under
  | is
  | name (n : Name)
  | unknown
deriving DecidableEq, Repr

def Op1.text : Op1 → String
  | .not => "not" | .len => "str.len"

def Op2.text : Op2 → String
  | .and => "and" | .or => "or" | .eq => "=" | .lt => "<" | .le => "<=" | .add => "+" | .sub => "-" | .mul => "*"
  | .div => "div" | .mod => "mod" | .cat => "str.++" | .slt => "str.<"

def symbols : List (String × Sym) :=
  [("not", .op1 .not), ("str.len", .op1 .len), ("and", .op2 .and), ("or", .op2 .or), ("=", .op2 .eq),
   ("<", .op2 .lt), ("<=", .op2 .le), ("+", .op2 .add), ("-", .op2 .sub), ("*", .op2 .mul), ("div", .op2 .div),
   ("mod", .op2 .mod), ("str.++", .op2 .cat), ("str.<", .op2 .slt), ("ite", .ite), ("true", .lit true), ("false", .lit false),
   ("_", .under), ("is", .is)]

-- A symbol the table does not list is unknown, which the default says.
set_option linter.tazuna.silentDefault false in
def classify (s : String) : Sym :=
  match Name.read s.toList with
  | some n => .name n
  | none => (symbols.lookup s).getD .unknown

def Op1.mk : Op1 → Term → Term
  | .not => .not | .len => .len

def Op2.mk : Op2 → Term → Term → Term
  | .and => .and | .or => .or | .eq => .eq | .lt => .lt | .le => .le | .add => .add | .sub => .sub | .mul => .mul
  | .div => .div | .mod => .mod | .cat => .cat | .slt => .slt

mutual
def Term.toSExp : Term → SExp
  | .var n => .sym (Name.var n).text
  | .int n => if 0 ≤ n then .num n.toNat else .list [.sym "-", .num n.natAbs]
  | .str s => .str s
  | .bool b => .sym (if b then "true" else "false")
  | .not a => .list [.sym "not", a.toSExp]
  | .len a => .list [.sym "str.len", a.toSExp]
  | .and a b => .list [.sym "and", a.toSExp, b.toSExp]
  | .or a b => .list [.sym "or", a.toSExp, b.toSExp]
  | .eq a b => .list [.sym "=", a.toSExp, b.toSExp]
  | .lt a b => .list [.sym "<", a.toSExp, b.toSExp]
  | .le a b => .list [.sym "<=", a.toSExp, b.toSExp]
  | .add a b => .list [.sym "+", a.toSExp, b.toSExp]
  | .sub a b => .list [.sym "-", a.toSExp, b.toSExp]
  | .mul a b => .list [.sym "*", a.toSExp, b.toSExp]
  | .div a b => .list [.sym "div", a.toSExp, b.toSExp]
  | .mod a b => .list [.sym "mod", a.toSExp, b.toSExp]
  | .cat a b => .list [.sym "str.++", a.toSExp, b.toSExp]
  | .slt a b => .list [.sym "str.<", a.toSExp, b.toSExp]
  | .ite c a b => .list [.sym "ite", c.toSExp, a.toSExp, b.toSExp]
  | .ctor d k [] => .sym (Name.ctor d k).text
  | .ctor d k (a :: as) => .list (.sym (Name.ctor d k).text :: Term.toSExps (a :: as))
  | .is d k a => .list [.list [.sym "_", .sym "is", .sym (Name.ctor d k).text], a.toSExp]
  | .sel d k j a => .list [.sym (Name.sel d k j).text, a.toSExp]
  | .ref i => .sym (Name.def_ i).text
  /- A script prints a shared term only as a reference to its definition (`Term.extract`), never this way. -/
  | .shared _ t => t.toSExp
def Term.toSExps : List Term → List SExp
  | [] => []
  | t :: ts => t.toSExp :: Term.toSExps ts
end

mutual
def Term.ofSExp : SExp → Option Term
  | .num n => some (.int n)
  | .str s => some (.str s)
  | .sym s => match classify s with
    | .lit b => some (.bool b)
    | .name (.var n) => some (.var n)
    | .name (.def_ i) => some (.ref i)
    | .name (.ctor d k) => some (.ctor d k [])
    | _ => none
  | .list [.sym f, a] => match classify f with
    | .op1 o => (Term.ofSExp a).map o.mk
    | .op2 .sub => match a with
      | .num n => some (.int (-(n : Int)))
      | _ => none
    | .name (.sel d k j) => (Term.ofSExp a).map (.sel d k j)
    | .name (.ctor d k) => (Term.ofSExp a).map fun t => .ctor d k [t]
    | _ => none
  | .list [.list [.sym u, .sym i, .sym c], a] =>
    match classify u, classify i, classify c with
    | .under, .is, .name (.ctor d k) => (Term.ofSExp a).map (.is d k)
    | _, _, _ => none
  | .list [.sym f, a, b] => match classify f with
    | .op2 o => do pure (o.mk (← Term.ofSExp a) (← Term.ofSExp b))
    | .name (.ctor d k) => do pure (.ctor d k [← Term.ofSExp a, ← Term.ofSExp b])
    | _ => none
  | .list [.sym f, c, a, b] => match classify f with
    | .ite => do pure (.ite (← Term.ofSExp c) (← Term.ofSExp a) (← Term.ofSExp b))
    | .name (.ctor d k) => do pure (.ctor d k [← Term.ofSExp c, ← Term.ofSExp a, ← Term.ofSExp b])
    | _ => none
  | .list (.sym f :: args) => match classify f with
    | .name (.ctor d k) => (Term.ofSExps args).map (.ctor d k)
    | _ => none
  | .list _ => none
def Term.ofSExps : List SExp → Option (List Term)
  | [] => some []
  | x :: xs => do pure ((← Term.ofSExp x) :: (← Term.ofSExps xs))
end

theorem readDigits_dec (acc : Nat) (ds : List Nat) (r : List Char) (h : ∀ d ∈ ds, d < 10)
    (hr : ∀ c ∈ r.head?, isDigit c = false) :
    readDigits acc (ds.map digitChar ++ r) = (ds.foldl (fun a d => a * 10 + d) acc, r) := by
  induction ds generalizing acc with
  | nil =>
    cases r with
    | nil => rfl
    | cons c cs => simp only [List.map_nil, List.nil_append, readDigits, hr c (by simp)]; rfl
  | cons d ds ih =>
    have hd := digitChar_facts ⟨d, h d (by simp)⟩
    simp only [List.map_cons, List.cons_append, readDigits, hd.1, hd.2, ite_true, List.foldl_cons]
    exact ih _ (fun x hx => h x (by simp [hx]))

theorem readNat_dec (n : Nat) (r : List Char) (hr : ∀ c ∈ r.head?, isDigit c = false) :
    readNat (decChars n ++ r) = some (n, r) := by
  have hlt := Tazuna.Ir.Literal.decimalDigits_lt n
  have hfold := Tazuna.Ir.Literal.foldl_decimalDigits n
  unfold decChars
  cases hds : decimalDigits n with
  | nil => rw [Tazuna.Ir.Literal.decimalDigits] at hds; split at hds <;> simp at hds
  | cons d ds =>
    rw [hds] at hlt hfold
    have hd := digitChar_facts ⟨d, hlt d (by simp)⟩
    simp only [List.map_cons, List.cons_append, readNat, hd.1, hd.2, ite_true]
    rw [readDigits_dec d ds r (fun x hx => hlt x (by simp [hx])) hr]
    simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add] at hfold
    rw [hfold]

theorem underscore_not_digit : isDigit '_' = false := by decide

theorem Name.read_chars (nm : Name) : Name.read nm.chars = some nm := by
  cases nm with
  | var n => simp only [Name.chars, Name.read]; rw [show decChars n = decChars n ++ [] from by simp,
      readNat_dec n [] (by simp)]
  | def_ i => simp only [Name.chars, Name.read]; rw [show decChars i = decChars i ++ [] from by simp,
      readNat_dec i [] (by simp)]
  | ctor d k =>
    simp only [Name.chars, List.cons_append, Name.read]
    rw [readNat_dec d _ (by simp [underscore_not_digit])]
    simp only
    rw [show decChars k = decChars k ++ [] from by simp, readNat_dec k [] (by simp)]
  | sel d k j =>
    simp only [Name.chars, List.cons_append, List.append_assoc, Name.read]
    rw [readNat_dec d _ (by simp [underscore_not_digit])]
    simp only
    rw [readNat_dec k _ (by simp [underscore_not_digit])]
    simp only
    rw [show decChars j = decChars j ++ [] from by simp, readNat_dec j [] (by simp)]

theorem classify_name (nm : Name) : classify nm.text = .name nm := by
  simp [classify, Name.text, String.toList_ofList, Name.read_chars]

theorem classify_fixed : classify "not" = .op1 .not ∧ classify "str.len" = .op1 .len ∧ classify "and" = .op2 .and ∧
    classify "or" = .op2 .or ∧ classify "=" = .op2 .eq ∧ classify "<" = .op2 .lt ∧ classify "<=" = .op2 .le ∧
    classify "+" = .op2 .add ∧ classify "-" = .op2 .sub ∧ classify "*" = .op2 .mul ∧ classify "div" = .op2 .div ∧
    classify "mod" = .op2 .mod ∧ classify "str.++" = .op2 .cat ∧ classify "str.<" = .op2 .slt ∧ classify "ite" = .ite ∧
    classify "true" = .lit true ∧ classify "false" = .lit false ∧ classify "_" = .under ∧ classify "is" = .is := by
  decide

mutual
/-- Whether the printer writes the term as itself: every string literal lies in the SMT-LIB string domain, and no
shared term is in it (a script prints those as references to its definitions). -/
def Term.inDomain : Term → Bool
  | .str s => Tazuna.inDomain s
  | .var _ | .int _ | .bool _ | .ref _ => true
  | .shared .. => false
  | .not a | .len a | .is _ _ a | .sel _ _ _ a => a.inDomain
  | .and a b | .or a b | .eq a b | .lt a b | .le a b | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .cat a b | .slt a b => a.inDomain && b.inDomain
  | .ite c a b => c.inDomain && a.inDomain && b.inDomain
  | .ctor _ _ args => Term.inDomains args
def Term.inDomains : List Term → Bool
  | [] => true
  | t :: ts => t.inDomain && Term.inDomains ts
end

mutual
theorem Term.ofSExp_toSExp : (t : Term) → t.inDomain = true → Term.ofSExp t.toSExp = some t
  | .var n, _ => by simp [Term.toSExp, Term.ofSExp, classify_name]
  | .ref i, _ => by simp [Term.toSExp, Term.ofSExp, classify_name]
  | .int n, _ => by
    by_cases h : 0 ≤ n
    · simp [Term.toSExp, Term.ofSExp, h]; omega
    · simp [Term.toSExp, Term.ofSExp, h, classify_fixed]; omega
  | .str s, _ => by simp [Term.toSExp, Term.ofSExp]
  | .bool b, _ => by cases b <;> simp [Term.toSExp, Term.ofSExp, classify_fixed]
  | .shared .., h => by simp [Term.inDomain] at h
  | .not a, h => by
    simp only [Term.inDomain] at h
    simp [Term.toSExp, Term.ofSExp, classify_fixed, Term.ofSExp_toSExp a h, Op1.mk]
  | .len a, h => by
    simp only [Term.inDomain] at h
    simp [Term.toSExp, Term.ofSExp, classify_fixed, Term.ofSExp_toSExp a h, Op1.mk]
  | .and a b, h | .or a b, h | .eq a b, h | .lt a b, h | .le a b, h | .add a b, h | .sub a b, h | .mul a b, h
  | .div a b, h | .mod a b, h | .cat a b, h | .slt a b, h => by
    simp only [Term.inDomain, Bool.and_eq_true] at h
    simp [Term.toSExp, Term.ofSExp, classify_fixed, Term.ofSExp_toSExp a h.1, Term.ofSExp_toSExp b h.2, Op2.mk]
  | .ite c a b, h => by
    simp only [Term.inDomain, Bool.and_eq_true] at h
    simp [Term.toSExp, Term.ofSExp, classify_fixed, Term.ofSExp_toSExp c h.1.1, Term.ofSExp_toSExp a h.1.2,
      Term.ofSExp_toSExp b h.2]
  | .ctor d k [], _ => by simp [Term.toSExp, Term.ofSExp, classify_name]
  | .ctor d k [a], h => by
    simp only [Term.inDomain, Term.inDomains, Bool.and_eq_true] at h
    simp [Term.toSExp, Term.toSExps, Term.ofSExp, classify_name, Term.ofSExp_toSExp a h.1]
  | .ctor d k [a, b], h => by
    simp only [Term.inDomain, Term.inDomains, Bool.and_eq_true] at h
    simp [Term.toSExp, Term.toSExps, Term.ofSExp, classify_name, Term.ofSExp_toSExp a h.1, Term.ofSExp_toSExp b h.2.1]
  | .ctor d k [a, b, c], h => by
    simp only [Term.inDomain, Term.inDomains, Bool.and_eq_true] at h
    simp [Term.toSExp, Term.toSExps, Term.ofSExp, classify_name, Term.ofSExp_toSExp a h.1, Term.ofSExp_toSExp b h.2.1,
      Term.ofSExp_toSExp c h.2.2.1]
  | .ctor d k (a :: b :: c :: e :: rest), h => by
    simp only [Term.inDomain] at h
    have := Term.ofSExps_toSExps (a :: b :: c :: e :: rest) h
    simp only [Term.toSExp, Term.toSExps] at this ⊢
    simp [Term.ofSExp, classify_name, this]
  | .is d k a, h => by
    simp only [Term.inDomain] at h
    simp [Term.toSExp, Term.ofSExp, classify_fixed, classify_name, Term.ofSExp_toSExp a h]
  | .sel d k j a, h => by
    simp only [Term.inDomain] at h
    simp [Term.toSExp, Term.ofSExp, classify_name, Term.ofSExp_toSExp a h]
theorem Term.ofSExps_toSExps : (ts : List Term) → Term.inDomains ts = true → Term.ofSExps (Term.toSExps ts) = some ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Term.inDomains, Bool.and_eq_true] at h
    simp [Term.toSExps, Term.ofSExps, Term.ofSExp_toSExp t h.1, Term.ofSExps_toSExps ts h.2]
end

/-! Printing and reading whole terms and values. -/

/-- Whether the printer writes the symbol as itself: simple, not starting with a digit. -/
def simpleSym (s : String) : Bool :=
  match s.toList with
  | c :: cs => !isDigit c && isSymChar c && cs.all isSymChar
  | [] => false

theorem simpleSym_wf (s : String) (h : simpleSym s = true) : (Token.sym s).wf := by
  unfold simpleSym at h
  split at h
  · rename_i c cs hs
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    exact ⟨c, cs, hs, h.1.1, h.1.2, h.2⟩
  · simp at h

mutual
/-- Whether every symbol is simple and every string in the SMT-LIB domain. -/
def SExp.ok : SExp → Bool
  | .sym s => simpleSym s
  | .num _ => true
  | .str s => inDomain s
  | .list xs => SExp.oks xs
def SExp.oks : List SExp → Bool
  | [] => true
  | x :: xs => x.ok && SExp.oks xs
end

mutual
theorem SExp.ok_wf : (e : SExp) → e.ok = true → ∀ t ∈ e.tokens, t.wf
  | .sym s, h, t, ht => by simp [SExp.tokens] at ht; subst ht; exact simpleSym_wf s h
  | .num _, _, t, ht => by simp [SExp.tokens] at ht; subst ht; trivial
  | .str s, h, t, ht => by
    simp [SExp.tokens] at ht; subst ht
    simpa [SExp.ok, inDomain, Token.wf] using h
  | .list xs, h, t, ht => by
    simp only [SExp.tokens, List.mem_cons, List.mem_append] at ht
    rcases ht with (rfl | ht) | ht
    · trivial
    · exact SExp.oks_wf xs h t ht
    · simp at ht; subst ht; trivial
theorem SExp.oks_wf : (xs : List SExp) → SExp.oks xs = true → ∀ t ∈ SExp.tokensList xs, t.wf
  | [], _, t, ht => by simp [SExp.tokensList] at ht
  | x :: xs, h, t, ht => by
    simp only [SExp.oks, Bool.and_eq_true] at h
    simp only [SExp.tokensList, List.mem_append] at ht
    rcases ht with ht | ht
    · exact SExp.ok_wf x h.1 t ht
    · exact SExp.oks_wf xs h.2 t ht
end

theorem decChars_digits (n : Nat) : ∀ c ∈ decChars n, isDigit c = true ∧ isSymChar c = true := by
  intro c hc
  simp only [decChars, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  have key : ∀ e : Fin 10, isDigit (digitChar e) = true ∧ isSymChar (digitChar e) = true := by decide
  exact key ⟨d, Tazuna.Ir.Literal.decimalDigits_lt n d hd⟩

theorem simpleSym_name (nm : Name) : simpleSym nm.text = true := by
  have hu : isSymChar '_' = true := by decide
  have hd : ∀ n, ∀ x ∈ decChars n, isSymChar x = true := fun n x hx => (decChars_digits n x hx).2
  cases nm <;>
    simp [simpleSym, Name.text, Name.chars, String.toList_ofList, List.all_eq_true, hu,
      show isDigit 'v' = false from by decide, show isSymChar 'v' = true from by decide,
      show isDigit 'D' = false from by decide, show isSymChar 'D' = true from by decide,
      show isDigit 's' = false from by decide, show isSymChar 's' = true from by decide] <;>
    first | exact ⟨hd _, hd _, hd _⟩ | exact ⟨hd _, hd _⟩ | exact hd _

theorem simpleSym_fixed : simpleSym "not" ∧ simpleSym "str.len" ∧ simpleSym "and" ∧ simpleSym "or" ∧ simpleSym "=" ∧
    simpleSym "<" ∧ simpleSym "<=" ∧ simpleSym "+" ∧ simpleSym "-" ∧ simpleSym "*" ∧ simpleSym "div" ∧
    simpleSym "mod" ∧ simpleSym "str.++" ∧ simpleSym "str.<" ∧ simpleSym "ite" ∧ simpleSym "true" ∧ simpleSym "false" ∧
    simpleSym "_" ∧ simpleSym "is" := by decide

mutual
theorem Term.toSExp_ok : (t : Term) → t.inDomain = true → t.toSExp.ok = true
  | .var n, _ => by simp [Term.toSExp, SExp.ok, simpleSym_name]
  | .ref i, _ => by simp [Term.toSExp, SExp.ok, simpleSym_name]
  | .shared .., h => by simp [Term.inDomain] at h
  | .int n, _ => by
    by_cases h : 0 ≤ n <;> simp [Term.toSExp, SExp.ok, SExp.oks, h, simpleSym_fixed]
  | .str s, h => by simpa [Term.toSExp, SExp.ok, Term.inDomain] using h
  | .bool b, _ => by cases b <;> simp [Term.toSExp, SExp.ok, simpleSym_fixed]
  | .not a, h | .len a, h => by
    simp only [Term.inDomain] at h
    simp [Term.toSExp, SExp.ok, SExp.oks, simpleSym_fixed, Term.toSExp_ok a h]
  | .is d k a, h => by
    simp only [Term.inDomain] at h
    simp [Term.toSExp, SExp.ok, SExp.oks, simpleSym_fixed, simpleSym_name, Term.toSExp_ok a h]
  | .sel d k j a, h => by
    simp only [Term.inDomain] at h
    simp [Term.toSExp, SExp.ok, SExp.oks, simpleSym_name, Term.toSExp_ok a h]
  | .and a b, h | .or a b, h | .eq a b, h | .lt a b, h | .le a b, h | .add a b, h | .sub a b, h | .mul a b, h
  | .div a b, h | .mod a b, h | .cat a b, h | .slt a b, h => by
    simp only [Term.inDomain, Bool.and_eq_true] at h
    simp [Term.toSExp, SExp.ok, SExp.oks, simpleSym_fixed, Term.toSExp_ok a h.1, Term.toSExp_ok b h.2]
  | .ite c a b, h => by
    simp only [Term.inDomain, Bool.and_eq_true] at h
    simp [Term.toSExp, SExp.ok, SExp.oks, simpleSym_fixed, Term.toSExp_ok c h.1.1, Term.toSExp_ok a h.1.2,
      Term.toSExp_ok b h.2]
  | .ctor d k [], _ => by simp [Term.toSExp, SExp.ok, simpleSym_name]
  | .ctor d k (a :: as), h => by
    simp only [Term.inDomain] at h
    have := Term.toSExps_oks (a :: as) h
    simp only [Term.toSExp, SExp.ok, SExp.oks, simpleSym_name, Bool.true_and]
    exact this
theorem Term.toSExps_oks : (ts : List Term) → Term.inDomains ts = true → SExp.oks (Term.toSExps ts) = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Term.inDomains, Bool.and_eq_true] at h
    simp [Term.toSExps, SExp.oks, Term.toSExp_ok t h.1, Term.toSExps_oks ts h.2]
end

def Term.print (t : Term) : String := t.toSExp.print

def Term.parse (text : String) : Option Term := (SExp.parse text).bind Term.ofSExp

/-- Reading back a printed term gives it, when its strings lie in the SMT-LIB domain. -/
theorem Term.parse_print (t : Term) (h : t.inDomain = true) : Term.parse t.print = some t := by
  simp [Term.parse, Term.print, SExp.parse_print _ (SExp.ok_wf _ (Term.toSExp_ok t h)), Term.ofSExp_toSExp t h]

mutual
def Val.toTerm : Val → Term
  | .int n => .int n
  | .bool b => .bool b
  | .str s => .str s
  | .ctor d k args => .ctor d k (Val.toTerms args)
def Val.toTerms : List Val → List Term
  | [] => []
  | v :: vs => v.toTerm :: Val.toTerms vs
end

mutual
def Term.toVal : Term → Option Val
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | .str s => some (.str s)
  | .ctor d k args => (Term.toVals args).map (.ctor d k)
  | _ => none
def Term.toVals : List Term → Option (List Val)
  | [] => some []
  | t :: ts => do pure ((← t.toVal) :: (← Term.toVals ts))
end

mutual
theorem Val.toVal_toTerm : (v : Val) → v.toTerm.toVal = some v
  | .int _ | .bool _ | .str _ => rfl
  | .ctor d k args => by simp [Val.toTerm, Term.toVal, Val.toVals_toTerms args]
theorem Val.toVals_toTerms : (vs : List Val) → Term.toVals (Val.toTerms vs) = some vs
  | [] => rfl
  | v :: vs => by simp [Val.toTerms, Term.toVals, Val.toVal_toTerm v, Val.toVals_toTerms vs]
end

def Val.print (v : Val) : String := v.toTerm.print

def Val.ofSExp (e : SExp) : Option Val := (Term.ofSExp e).bind Term.toVal

def Val.parse (text : String) : Option Val := (Term.parse text).bind Term.toVal

/-- Reading back a printed value gives it, when its strings lie in the SMT-LIB domain. -/
theorem Val.parse_print (v : Val) (h : v.toTerm.inDomain = true) : Val.parse v.print = some v := by
  simp [Val.parse, Val.print, Term.parse_print _ h, Val.toVal_toTerm]

end Tazuna.Smt
