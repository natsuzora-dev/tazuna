/-! Gleam's literal tokens. The IR carries an Int or String literal as the exact source text, and Lean reads it here by
Gleam's lexical rules, so the converter never decides what a literal means. -/

namespace Tazuna.Ir.Literal

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def digitIn (radix : Nat) (c : Char) : Option Nat :=
  (hexValue c).filter (· < radix)

/-- The digits after the first: an underscore may stand between two digits, never twice or at the end. -/
def digitsFrom (radix : Nat) : Nat → List Char → Option Nat
  | acc, [] => some acc
  | acc, c :: cs =>
    if c = '_' then
      match cs with
      | d :: ds => (digitIn radix d).bind fun v => digitsFrom radix (acc * radix + v) ds
      | [] => none
    else (digitIn radix c).bind fun v => digitsFrom radix (acc * radix + v) cs

def digits (radix : Nat) : List Char → Option Nat
  | c :: cs => (digitIn radix c).bind fun v => digitsFrom radix v cs
  | [] => none

def radixOf (c : Char) : Option Nat :=
  if c = 'x' ∨ c = 'X' then some 16
  else if c = 'o' ∨ c = 'O' then some 8
  else if c = 'b' ∨ c = 'B' then some 2
  else none

/-- `0x`, `0o` and `0b` may be followed by one underscore before the digits. -/
def unsigned (cs : List Char) : Option Nat :=
  match cs with
  | '0' :: c :: rest =>
    match radixOf c with
    | some r => match rest with
      | '_' :: ds => digits r ds
      | ds => digits r ds
    | none => digits 10 cs
  | _ => digits 10 cs

/-- Reads an Int token such as `1_000`, `0xFF` or `-12`. Gleam's Ints are unbounded (the Erlang target). -/
def parseInt (text : String) : Option Int :=
  match text.toList with
  | '-' :: cs => (unsigned cs).map fun n => -Int.ofNat n
  | cs => (unsigned cs).map Int.ofNat

def decimalDigits (n : Nat) : List Nat :=
  if n < 10 then [n] else decimalDigits (n / 10) ++ [n % 10]
termination_by n
decreasing_by omega

def digitChar (d : Nat) : Char := Char.ofNat ('0'.toNat + d)

def printInt (n : Int) : String :=
  let body := String.ofList ((decimalDigits n.natAbs).map digitChar)
  if n < 0 then "-" ++ body else body

/-- Where the lexer is inside a String token's body. -/
inductive StrState where
  | body
  | escape
  | unicodeOpen
  | unicodeHex (value count : Nat)
  | closed

/-- One character of a String token: the next state and the character it contributes, if any. Gleam's escapes are
`\"`, `\\`, `\f`, `\n`, `\r`, `\t` and `\u{...}` with one to six hex digits naming a Unicode scalar value. -/
def strStep : StrState → Char → Option (StrState × Option Char)
  | .body, c =>
    if c = '"' then some (.closed, none)
    else if c = '\\' then some (.escape, none)
    else some (.body, some c)
  | .escape, c =>
    if c = '"' then some (.body, some '"')
    else if c = '\\' then some (.body, some '\\')
    else if c = 'f' then some (.body, some (Char.ofNat 12))
    else if c = 'n' then some (.body, some '\n')
    else if c = 'r' then some (.body, some '\r')
    else if c = 't' then some (.body, some '\t')
    else if c = 'u' then some (.unicodeOpen, none)
    else none
  | .unicodeOpen, c => if c = '{' then some (.unicodeHex 0 0, none) else none
  | .unicodeHex value count, c =>
    if c = '}' then
      if 0 < count ∧ (Char.ofNat value).toNat = value then some (.body, some (Char.ofNat value)) else none
    else match hexValue c with
      | some d => if count < 6 then some (.unicodeHex (value * 16 + d) (count + 1), none) else none
      | none => none
  | .closed, _ => none

def strFrom : StrState → List Char → Option (List Char)
  | .closed, [] => some []
  | _, [] => none
  | s, c :: cs =>
    match strStep s c with
    | some (s', out) => (strFrom s' cs).map (out.toList ++ ·)
    | none => none

/-- Reads a String token, quotes included. -/
def parseStr (text : String) : Option String :=
  match text.toList with
  | '"' :: cs => (strFrom .body cs).map String.ofList
  | _ => none

def escapeChar (c : Char) : List Char :=
  if c = '"' then ['\\', '"'] else if c = '\\' then ['\\', '\\'] else [c]

def printStr (s : String) : String :=
  String.ofList ('"' :: s.toList.flatMap escapeChar ++ ['"'])

theorem digitIn_digitChar (d : Nat) (h : d < 10) : digitIn 10 (digitChar d) = some d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

theorem digitChar_ne_underscore (d : Nat) (h : d < 10) : digitChar d ≠ '_' := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

theorem decimalDigits_lt (n : Nat) : ∀ d ∈ decimalDigits n, d < 10 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decimalDigits]
    split
    · intro d hd; simp at hd; omega
    · intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | hd
      · exact ih (n / 10) (by omega) d hd
      · omega

theorem digitsFrom_map (acc : Nat) (ds : List Nat) (h : ∀ d ∈ ds, d < 10) :
    digitsFrom 10 acc (ds.map digitChar) = some (ds.foldl (fun a d => a * 10 + d) acc) := by
  induction ds generalizing acc with
  | nil => rfl
  | cons d ds ih =>
    have hd := h d (by simp)
    rw [List.map_cons]
    unfold digitsFrom
    rw [ite_eq_right_of_eq_false _ _ (eq_false (digitChar_ne_underscore d hd)), digitIn_digitChar d hd]
    simp only [Option.bind_some, List.foldl_cons]
    exact ih _ (fun x hx => h x (by simp [hx]))

theorem foldl_decimalDigits (n : Nat) : (decimalDigits n).foldl (fun a d => a * 10 + d) 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [decimalDigits]
    split
    · simp
    · rw [List.foldl_append, ih (n / 10) (by omega)]
      simp only [List.foldl_cons, List.foldl_nil]
      omega

theorem digits_decimal (n : Nat) : digits 10 ((decimalDigits n).map digitChar) = some n := by
  have hlt := decimalDigits_lt n
  have hfold := foldl_decimalDigits n
  cases hds : decimalDigits n with
  | nil => rw [decimalDigits] at hds; split at hds <;> simp at hds
  | cons d ds =>
    rw [hds] at hlt hfold
    have hd := hlt d (by simp)
    simp only [List.map_cons, digits, digitIn_digitChar d hd, Option.bind_some]
    rw [digitsFrom_map d ds (fun x hx => hlt x (by simp [hx]))]
    simpa using hfold

theorem radixOf_digitChar (d : Nat) (h : d < 10) : radixOf (digitChar d) = none := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

theorem unsigned_decimal (n : Nat) : unsigned ((decimalDigits n).map digitChar) = some n := by
  have hlt := decimalDigits_lt n
  unfold unsigned
  split
  · rename_i c rest heq
    have hc : radixOf c = none := by
      cases hds : decimalDigits n with
      | nil => rw [hds] at heq; simp at heq
      | cons d ds =>
        cases ds with
        | nil => rw [hds] at heq; simp at heq
        | cons e es =>
          rw [hds] at heq hlt
          simp only [List.map_cons, List.cons.injEq] at heq
          rw [← heq.2.1]
          exact radixOf_digitChar e (hlt e (by simp))
    rw [hc]
    exact digits_decimal n
  · exact digits_decimal n

theorem digitChar_ne_minus (d : Nat) (h : d < 10) : digitChar d ≠ '-' := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

/-- Reading back a printed Int gives the same Int. -/
theorem parseInt_printInt (n : Int) : parseInt (printInt n) = some n := by
  have hlt := decimalDigits_lt n.natAbs
  by_cases hneg : n < 0
  · have hs : (printInt n).toList = '-' :: (decimalDigits n.natAbs).map digitChar := by simp [printInt, hneg]
    rw [parseInt, hs]
    simp only [unsigned_decimal, Option.map_some]
    congr 1
    rw [Int.ofNat_eq_natCast]
    omega
  · have hs : (printInt n).toList = (decimalDigits n.natAbs).map digitChar := by simp [printInt, hneg]
    rw [parseInt, hs]
    split
    · rename_i cs heq
      cases hds : decimalDigits n.natAbs with
      | nil => rw [hds] at heq; simp at heq
      | cons d ds =>
        rw [hds] at heq hlt
        simp only [List.map_cons, List.cons.injEq] at heq
        exact absurd heq.1 (digitChar_ne_minus d (hlt d (by simp)))
    · rw [unsigned_decimal]
      simp only [Option.map_some]
      congr 1
      rw [Int.ofNat_eq_natCast]
      omega

theorem strFrom_escaped (cs : List Char) : strFrom .body (cs.flatMap escapeChar ++ ['"']) = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, List.append_assoc]
    by_cases h₁ : c = '"'
    · subst h₁
      show strFrom .body ('\\' :: '"' :: (cs.flatMap escapeChar ++ ['"'])) = some ('"' :: cs)
      simp (config := { decide := true }) [strFrom, strStep, ih]
    · by_cases h₂ : c = '\\'
      · subst h₂
        show strFrom .body ('\\' :: '\\' :: (cs.flatMap escapeChar ++ ['"'])) = some ('\\' :: cs)
        simp (config := { decide := true }) [strFrom, strStep, ih]
      · have he : escapeChar c = [c] := by simp [escapeChar, h₁, h₂]
        rw [he]
        show strFrom .body (c :: (cs.flatMap escapeChar ++ ['"'])) = some (c :: cs)
        simp [strFrom, strStep, h₁, h₂, ih]

/-- Reading back a printed String gives the same String. -/
theorem parseStr_printStr (s : String) : parseStr (printStr s) = some s := by
  unfold parseStr printStr
  simp only [String.toList_ofList, List.cons_append]
  rw [strFrom_escaped]
  simp [String.ofList_toList]

#guard parseInt "1_000_000_000_000_000_000_000" = some 1000000000000000000000
#guard parseInt "123456789012345678901234567890" = some 123456789012345678901234567890
#guard parseInt "-1_0" = some (-10)
#guard parseInt "0xff_FF" = some 65535
#guard parseInt "0x_1" = some 1
#guard parseInt "0o17" = some 15
#guard parseInt "0B101" = some 5
#guard parseInt "007" = some 7
#guard ["1__0", "1_", "_1", "0_", "0x", "0x__1", "0x1_", "0b12", "0o8", "1e3", "+1", ""].all
    (parseInt · = none)

#guard parseStr "\"a\\u{1F600}\\u{10FFFF}\\u{0}\"" = some (String.ofList ['a', Char.ofNat 0x1F600, Char.ofNat 0x10FFFF, Char.ofNat 0])
#guard parseStr "\"\\\"\\\\\\f\\n\\r\\t\"" = some "\"\\\x0c\n\r\t"
#guard parseStr "\"line\nbreak\"" = some "line\nbreak"
#guard parseStr "\"\\u{000041}\"" = some "A"
#guard ["\"\\e\"", "\"\\u{D800}\"", "\"\\u{110000}\"", "\"\\u{0000041}\"", "\"\\u{}\"", "\"\\u41\"",
    "\"\\'\"", "\"a\"b\"", "\"open", "bare"].all (parseStr · = none)

end Tazuna.Ir.Literal
