import Tazuna.Data.Value

namespace Tazuna.Data

/-- Milliseconds since the Unix epoch. -/
abbrev Time := Int

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

/-- The code point of character `i` of `s`, or -1 past its end, as SMT-LIB's `str.to_code (str.at s i)` gives it. -/
def codeAt (s : String) (i : Nat) : Int := (s.toList[i]?.map (fun c => (c.toNat : Int))).getD (-1)

/-- The digit that character `i` of `s` is, when it is one. -/
def digitAt (s : String) (i : Nat) : Int := codeAt s i - 48

def isDigitAt (s : String) (i : Nat) : Bool := 0 ≤ digitAt s i && digitAt s i ≤ 9

def isLeap (y : Int) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def monthDays (y m : Int) : Int :=
  if m == 2 then (if isLeap y then 29 else 28) else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

/-- The year, month and day that the digits of a label `YYYY-MM-DD` write. -/
def labelYear (s : String) : Int := digitAt s 0 * 1000 + digitAt s 1 * 100 + digitAt s 2 * 10 + digitAt s 3
def labelMonth (s : String) : Int := digitAt s 5 * 10 + digitAt s 6
def labelDay (s : String) : Int := digitAt s 8 * 10 + digitAt s 9

/--
Whether `s` is a label `YYYY-MM-DD` of a real day in years 0000 through 9999. Smt.dateValid states the same of a term,
character by character, so that the two agree by their definitions.
-/
def isDateLabel (s : String) : Bool :=
  s.length == 10 && isDigitAt s 0 && isDigitAt s 1 && isDigitAt s 2 && isDigitAt s 3 && codeAt s 4 == 45 &&
    isDigitAt s 5 && isDigitAt s 6 && codeAt s 7 == 45 && isDigitAt s 8 && isDigitAt s 9 &&
    1 ≤ labelMonth s && labelMonth s ≤ 12 && 1 ≤ labelDay s && labelDay s ≤ monthDays (labelYear s) (labelMonth s)

/-- The days since 1970-01-01 of a date label `YYYY-MM-DD` of a real day in years 0000 through 9999. -/
def parseDate? (text : String) : Option Int :=
  if isDateLabel text then some (daysFromCivil (labelYear text) (labelMonth text) (labelDay text)) else none

/-- The one-digit string of the last decimal digit of `n`. -/
def digitChar (n : Int) : String := String.singleton (Char.ofNat (48 + n % 10).toNat)

/-- The label `YYYY-MM-DD` of a year from 0000 through 9999, a month and a day. -/
def dateLabel (y m d : Int) : String :=
  digitChar (y / 1000) ++ digitChar (y / 100) ++ digitChar (y / 10) ++ digitChar y ++ "-" ++ digitChar (m / 10) ++
    digitChar m ++ "-" ++ digitChar (d / 10) ++ digitChar d

/-- The label `YYYY-MM-DD` of the day `days` after 1970-01-01, when its year is 0000 through 9999. -/
def renderDate? (days : Int) : Option String :=
  let (y, m, d) := civilFromDays days
  if 0 ≤ y && y ≤ 9999 then some (dateLabel y m d) else none

/-- The first and the last day that a label names, 0000-01-01 and 9999-12-31. -/
def firstDay : Int := -719528
def lastDay : Int := 2932896

/-- Whether `t` is a safe integer, as an instant on the wire must be. -/
def Time.inRange (t : Time) : Bool := isSafeInteger t

/-- `t`, when it is in range (Time.inRange). -/
def instantTime? (t : Time) : Option Time := if t.inRange then some t else none

end Tazuna.Data
