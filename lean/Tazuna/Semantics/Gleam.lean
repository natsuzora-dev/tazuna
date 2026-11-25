import Tazuna.Linter

/-! Gleam's meaning for the operators whose edges differ between languages. A spec means what Gleam on Erlang means
(design, Revision 1). Where the Gleam language tour states the rule, the comment cites it; where it does not, the rule
was observed by running gleam 1.19.2 on both targets (`-7 / 2 = -3`, `-7 % 2 = -1`, `7 / -2 = -3`, `7 % -2 = 1`,
`7 / 0 = 0`, `7 % 0 = 0`). -/

namespace Tazuna.Gleam

/-- Gleam's `/` on Int. -/
def div (a b : Int) : Int := a.tdiv b

/-- Gleam's `%` on Int. -/
def mod (a b : Int) : Int := if b = 0 then 0 else a.tmod b

/-- `tazuna.length`: the number of code points. Gleam's own `string.length` counts graphemes instead; tazuna counts
code points because SMT strings are sequences of code points. -/
def length (s : String) : Int := s.length

-- Observed on gleam 1.19.2, both targets: dividing by zero gives zero (the tour states this for Float only).
theorem div_zero (a : Int) : div a 0 = 0 := by simp [div]

-- Observed on gleam 1.19.2, both targets: the remainder by zero is zero, unlike Lean's `Int.tmod a 0 = a`.
theorem mod_zero (a : Int) : mod a 0 = 0 := by simp [mod]

-- Observed on gleam 1.19.2: `/` truncates toward zero, so `/` and `%` split every Int.
theorem div_add_mod (a b : Int) (h : b ≠ 0) : b * div a b + mod a b = a := by
  simp [div, mod, h, Int.mul_tdiv_add_tmod]

-- Observed on gleam 1.19.2: the remainder takes the sign of the dividend.
theorem mod_neg_left (a b : Int) : mod (-a) b = -mod a b := by
  unfold mod; split <;> simp [Int.neg_tmod]

theorem mod_neg_right (a b : Int) : mod a (-b) = mod a b := by
  unfold mod; split <;> simp_all [Int.tmod_neg]

theorem div_neg_right (a b : Int) : div a (-b) = -div a b := by simp [div, Int.tdiv_neg]

-- The Gleam tour (basics/ints): "When running on the Erlang virtual machine ints have no maximum and minimum size."
-- Int is Lean's unbounded Int, so no operation wraps:
example : (2 : Int) ^ 64 + 1 > 2 ^ 64 := by decide

example : div (-7) 2 = -3 := by decide
example : mod (-7) 2 = -1 := by decide
example : div 7 (-2) = -3 := by decide
example : mod 7 (-2) = 1 := by decide
example : div 7 0 = 0 := by decide
example : mod 7 0 = 0 := by decide

theorem length_eq_codepoints (s : String) : length s = s.toList.length := by simp [length, String.length]

-- "e" followed by U+0301 COMBINING ACUTE ACCENT is one grapheme and two code points.
#guard length "é" == 2
#guard length "😀" == 1

end Tazuna.Gleam
