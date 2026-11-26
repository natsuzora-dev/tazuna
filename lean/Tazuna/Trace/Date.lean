import Tazuna.Ir.Literal

/-! Dates on the wire. A date is its day number since 1970-01-01; a trace writes it as the ISO 8601 label of its
proleptic Gregorian day, `YYYY-MM-DD` for years 0000 through 9999 and the expanded year form outside them, so every
day has a label (`Tazuna.Trace.DateThm`). -/

namespace Tazuna.Trace

open Tazuna.Ir.Literal (decimalDigits digitChar digitsFrom)

/-- Days since 1970-01-01 of a proleptic Gregorian date (Howard Hinnant's days_from_civil). -/
def daysFromCivil (y m d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let doy := (153 * (if m > 2 then m - 3 else m + 9) + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The inverse of `daysFromCivil` (Hinnant's civil_from_days). -/
def civilFromDays (z : Int) : Int × Int × Int :=
  let z := z + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if decide (mp < 10) then mp + 3 else mp - 9
  (if decide (m ≤ 2) then yoe + era * 400 + 1 else yoe + era * 400, m, d)

def isLeap (y : Int) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def monthDays (y m : Int) : Int :=
  if m == 2 then (if isLeap y then 29 else 28) else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

/-- The digits of `n`, with zeros in front up to `width` digits. -/
def padded (width n : Nat) : List Char :=
  (List.replicate (width - (decimalDigits n).length) 0 ++ decimalDigits n).map digitChar

/-- A year from 0000 through 9999 is four digits; any other year is a sign and at least six digits, the ISO 8601
expanded form that JavaScript's toISOString writes (`+275760`, `-000001`). -/
def yearChars (y : Int) : List Char :=
  if 0 ≤ y ∧ y ≤ 9999 then padded 4 y.toNat else if y < 0 then '-' :: padded 6 y.natAbs else '+' :: padded 6 y.toNat

def twoDigits (n : Nat) : List Char := [digitChar (n / 10), digitChar (n % 10)]

/-- The label of the day `days` after 1970-01-01: its year, then `-MM-DD`. Every day has one. -/
def renderDate (days : Int) : String :=
  let (y, m, d) := civilFromDays days
  String.ofList (yearChars y ++ '-' :: twoDigits m.toNat ++ '-' :: twoDigits d.toNat)

/-- The year that a year's characters write, read loosely; `parseDate?` keeps only the text `renderDate` writes. -/
def readYear : List Char → Option Int
  | [] => none
  | c :: cs =>
    if c = '-' then (digitsFrom 10 0 cs).map fun n => -Int.ofNat n
    else if c = '+' then (digitsFrom 10 0 cs).map Int.ofNat
    else (digitsFrom 10 0 (c :: cs)).map Int.ofNat

/-- The day that a label's year and its last six characters `-MM-DD` write, read loosely. -/
def readDate (cs : List Char) : Option Int :=
  match cs.reverse with
  | d2 :: d1 :: '-' :: m2 :: m1 :: '-' :: year => do
    let y ← readYear year.reverse
    let m ← digitsFrom 10 0 [m1, m2]
    let d ← digitsFrom 10 0 [d1, d2]
    pure (daysFromCivil y m d)
  | _ => none

/-- The day a label names, when the label is the one `renderDate` writes for it. -/
def parseDate? (text : String) : Option Int :=
  (readDate text.toList).filter fun z => renderDate z == text

end Tazuna.Trace
