import Lean.Data.Json.Basic

/-!
Spec numbers are integers; JSON from JS writes an integer as its digits, with no fraction or exponent.
-/

namespace Tazuna.Semantics

def isInteger (n : Lean.JsonNumber) : Bool := n.mantissa % 10 ^ n.exponent == 0

/-- `n` without trailing zeros in its mantissa, the form in which a number that JS writes reads as JSON. -/
def trimmed (n : Lean.JsonNumber) : Lean.JsonNumber :=
  let zeros := ((toString n.mantissa.natAbs).toList.reverse.takeWhile (· == '0')).length
  let k := min zeros n.exponent
  ⟨n.mantissa / 10 ^ k, n.exponent - k⟩

/--
The text that JS's Number.prototype.toString writes for `x`, when `x` is the shortest decimal of its double, as JSON
from JS holds it.
-/
def jsNumber (x : Lean.JsonNumber) : String := Id.run do
  if x.mantissa == 0 then return "0"
  let digits := (toString x.mantissa.natAbs).toList
  let significant := (digits.reverse.dropWhile (· == '0')).reverse
  let k := significant.length
  let s := String.ofList significant
  let n : Int := (digits.length : Int) - x.exponent
  let zeros (count : Int) := String.ofList (List.replicate count.toNat '0')
  let split (point : Nat) := String.ofList (significant.take point) ++ "." ++ String.ofList (significant.drop point)
  let body :=
    if k ≤ n && n ≤ 21 then s ++ zeros (n - k)
    else if 0 < n && n ≤ 21 then split n.toNat
    else if -6 < n && n ≤ 0 then "0." ++ zeros (-n) ++ s
    else
      let e := n - 1
      let exp := (if e ≥ 0 then "+" else "-") ++ toString e.natAbs
      (if k == 1 then s else split 1) ++ "e" ++ exp
  return (if x.mantissa < 0 then "-" else "") ++ body

end Tazuna.Semantics
