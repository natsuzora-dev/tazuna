import Lean.Data.Json.Basic

/-!
JS numbers are IEEE binary64 doubles, which JSON from JS writes as the shortest decimal that reads back as the same
double. A decimal reads as a double by `JsonNumber.toFloat`, whose `Float.ofScientific` rounds correctly, and a double
writes back as that shortest decimal.
-/

namespace Tazuna.Data

/-- The exact value of a finite double as a decimal, which a double always has: `m · 2^e` is `m · 5^-e / 10^-e`. -/
def exactDecimal (x : Float) : Lean.JsonNumber :=
  let bits := x.toBits.toNat
  let biased := (bits >>> 52) % 2048
  let fraction := bits % 2 ^ 52
  let (m, e) : Nat × Int := if biased == 0 then (fraction, -1074) else (fraction + 2 ^ 52, biased - 1075)
  let magnitude : Lean.JsonNumber := if e ≥ 0 then ⟨m * 2 ^ e.toNat, 0⟩ else ⟨m * 5 ^ e.natAbs, e.natAbs⟩
  if bits ≥ 2 ^ 63 then ⟨-magnitude.mantissa, magnitude.exponent⟩ else magnitude

/-- `n` without trailing zeros in its mantissa, the form in which a decimal that JS writes reads as JSON. -/
def trimmed (n : Lean.JsonNumber) : Lean.JsonNumber :=
  let zeros := ((toString n.mantissa.natAbs).toList.reverse.takeWhile (· == '0')).length
  let k := min zeros n.exponent
  ⟨n.mantissa / 10 ^ k, n.exponent - k⟩

/--
`n` rounded to `p` significant digits, ties to even: of the decimals of `p` digits, the nearest, as JS's
Number::toString picks among the shortest that read back as the double.
-/
def roundDigits (n : Lean.JsonNumber) (p : Nat) : Lean.JsonNumber :=
  let m := n.mantissa.natAbs
  let drop := (toString m).length - p
  if (toString m).length ≤ p then n else
  let unit := 10 ^ drop
  let (q, r) := (m / unit, m % unit)
  let q := if 2 * r > unit || (2 * r == unit && q % 2 == 1) then q + 1 else q
  let scaled : Int := if drop ≤ n.exponent then q else q * 10 ^ (drop - n.exponent)
  ⟨if n.mantissa < 0 then -scaled else scaled, n.exponent - min drop n.exponent⟩

/--
The decimal that JSON from JS holds for a finite double: the shortest that reads back as it, none for an infinity or
NaN, which JSON.stringify writes as null. A negative zero is zero, as JSON.stringify writes it.
-/
def decimalOf? (x : Float) : Option Lean.JsonNumber :=
  if x.isNaN || x.isInf then none
  else if x == 0 then some ⟨0, 0⟩
  else
    let exact := exactDecimal x
    let found := (List.range 17).findSome? fun i =>
      let candidate := roundDigits exact (i + 1)
      if candidate.toFloat == x then some candidate else none
    some (trimmed (found.getD exact))

end Tazuna.Data
