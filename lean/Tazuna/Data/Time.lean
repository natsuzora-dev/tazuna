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

def digitsOf (s : String) : Except String Int :=
  if !s.isEmpty && s.all Char.isDigit then pure s.toNat!
  else throw s!"expected digits, got {s}"

/--
The time of a datetime such as `2026-10-25T09:00:00+09:00`. Seconds and their fraction are optional, and the fraction
is read to milliseconds.
-/
def parseTime (text : String) : Except String Time := do
  let fail : Except String Time := throw s!"{text} is not a datetime with an offset"
  let cs := text.toList
  if cs.length < 17 then fail else
  let part (a b : Nat) := digitsOf (String.ofList ((cs.drop a).take (b - a)))
  let (y, mo, d, h, mi) := (← part 0 4, ← part 5 7, ← part 8 10, ← part 11 13, ← part 14 16)
  let rest := cs.drop 16
  let (sec, rest) ← match rest with
    | ':' :: a :: b :: more => pure (← digitsOf (String.ofList [a, b]), more)
    | _ => pure (0, rest)
  let (ms, rest) ← match rest with
    | '.' :: more =>
      let fraction := more.takeWhile Char.isDigit
      let padded := ((fraction ++ ['0', '0', '0']).take 3)
      pure (← digitsOf (String.ofList padded), more.drop fraction.length)
    | _ => pure (0, rest)
  let offset ← match rest with
    | ['Z'] | ['z'] => pure 0
    | [sign, a, b, ':', c, e] =>
      let minutes := (← digitsOf (String.ofList [a, b])) * 60 + (← digitsOf (String.ofList [c, e]))
      if sign == '+' then pure minutes else if sign == '-' then pure (-minutes) else fail
    | _ => fail
  let days := daysFromCivil y mo d
  pure ((((days * 24 + h) * 60 + mi - offset) * 60 + sec) * 1000 + ms)

/-- The days since 1970-01-01 of a date such as `2026-10-25`. -/
def parseDate (text : String) : Except String Int := do
  let cs := text.toList
  if cs.length != 10 || cs[4]? != some '-' || cs[7]? != some '-' then throw s!"{text} is not a date"
  let part (a b : Nat) := digitsOf (String.ofList ((cs.drop a).take (b - a)))
  pure (daysFromCivil (← part 0 4) (← part 5 7) (← part 8 10))

def pad (width : Nat) (n : Int) : String :=
  let s := toString n.toNat
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-- The string of `Temporal.Instant.prototype.toString`: UTC, milliseconds without trailing zeros. -/
def renderTime (t : Time) : String :=
  let days := t / 86400000
  let ms := t % 86400000
  let (y, mo, d) := civilFromDays days
  let fraction := if ms % 1000 == 0 then "" else
    "." ++ String.ofList ((pad 3 (ms % 1000)).toList.reverse.dropWhile (· == '0')).reverse
  s!"{pad 4 y}-{pad 2 mo}-{pad 2 d}T{pad 2 (ms / 3600000)}:{pad 2 (ms / 60000 % 60)}:{pad 2 (ms / 1000 % 60)}{fraction}Z"

/-- The time of `text`, when renderTime writes that time back as `text`. -/
def instantTime? (text : String) : Option Time :=
  match parseTime text with
  | .ok t => if renderTime t == text then some t else none
  | .error _ => none

/-- An instant as the wire writes it, in the form that renderTime writes. Time is Int, so modules use it locally. -/
def Time.toValue (t : Time) : Value := .str (renderTime t)

def Time.fromValue (v : Value) : Except String Time := do parseTime (← FromValue.fromValue v)

/-- Whether Zod's `z.iso.datetime({ offset: true })` accepts `text`. -/
def isOffsetDateTime (text : String) : Bool :=
  let number (a b : Char) : Nat := (a.toNat - '0'.toNat) * 10 + (b.toNat - '0'.toNat)
  match text.toList with
  | y1 :: y2 :: y3 :: y4 :: '-' :: m1 :: m2 :: '-' :: d1 :: d2 :: 'T' :: h1 :: h2 :: ':' :: n1 :: n2 :: ':' :: s1 :: s2
      :: rest =>
    let year := number y1 y2 * 100 + number y3 y4
    let month := number m1 m2
    let leap := year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
    let days := if month == 2 then (if leap then 29 else 28) else if month ∈ [4, 6, 9, 11] then 30 else 31
    let offset := match rest with
      | '.' :: more =>
        let fraction := more.takeWhile Char.isDigit
        if fraction.isEmpty then [] else more.drop fraction.length
      | more => more
    [y1, y2, y3, y4, m1, m2, d1, d2, h1, h2, n1, n2, s1, s2].all Char.isDigit && 1 ≤ month && month ≤ 12 &&
      1 ≤ number d1 d2 && number d1 d2 ≤ days && number h1 h2 ≤ 23 && number n1 n2 ≤ 59 && number s1 s2 ≤ 59 &&
      match offset with
      | ['Z'] => true
      | [sign, a, b, ':', c, e] =>
        (sign == '+' || sign == '-') && [a, b, c, e].all Char.isDigit && number a b ≤ 23 && number c e ≤ 59
      | _ => false
  | _ => false

structure DateTime where
  text : String
  time : Time
deriving DecidableEq, Repr, Inhabited

instance : FromValue DateTime := ⟨fun
  | .str text =>
    if isOffsetDateTime text then do pure { text, time := ← parseTime text }
    else throw s!"{text} is not a date and time with seconds and an offset"
  | _ => throw "expected a date and time string"⟩

instance : ToValue DateTime := ⟨fun d => .str d.text⟩

end Tazuna.Data
