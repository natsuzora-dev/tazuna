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
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then yoe + era * 400 + 1 else yoe + era * 400, m, d)

def pad (width : Nat) (n : Int) : String :=
  let s := toString n.toNat
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-- The days since 1970-01-01 of a date label `YYYY-MM-DD` of a real day in years 0000 through 9999. -/
def parseDate? (text : String) : Option Int :=
  let number (a b : Char) : Nat := (a.toNat - '0'.toNat) * 10 + (b.toNat - '0'.toNat)
  match text.toList with
  | y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: [d1, d2] =>
    let year := number y1 y2 * 100 + number y3 y4
    let month := number m1 m2
    let day := number d1 d2
    let leap := year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
    let days := if month == 2 then (if leap then 29 else 28) else if month ∈ [4, 6, 9, 11] then 30 else 31
    if [y1, y2, y3, y4, m1, m2, d1, d2].all Char.isDigit && 1 ≤ month && month ≤ 12 && 1 ≤ day && day ≤ days then
      some (daysFromCivil year month day)
    else none
  | _ => none

/-- The label `YYYY-MM-DD` of the day `days` after 1970-01-01, when its year is 0000 through 9999. -/
def renderDate? (days : Int) : Option String :=
  let (y, m, d) := civilFromDays days
  if 0 ≤ y && y ≤ 9999 then some s!"{pad 4 y}-{pad 2 m}-{pad 2 d}" else none

/-- Whether `t` is a safe integer, as an instant on the wire must be. -/
def Time.inRange (t : Time) : Bool := isSafeInteger t

/-- `t`, when it is in range (Time.inRange). -/
def instantTime? (t : Time) : Option Time := if t.inRange then some t else none

end Tazuna.Data
