import Tazuna.Trace.Date

/-!
A date label and its day number are one value written two ways: every day has a label, and parseDate? and renderDate
are inverse (`render_parse`, `parse_render`). A trace's dates rest on these: a date is its day number, and its label is
what a trace writes.

The calendar repeats every 400 years. Within one cycle, the kernel checks each year's first and last day and each day of
a year that starts March 1 (`years`, `monthsForward`), and monotonicity of the year count covers the days
between.
-/

namespace Tazuna.Trace.DateThm

open Tazuna.Trace

/-- The year of a cycle that day `doe` of the cycle falls in, years starting March 1, as civilFromDays finds it. -/
def yoeOf (doe : Int) : Int := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365

/-- The first day of year `y` of a cycle. -/
def yearStart (y : Int) : Int := 365 * y + y / 4 - y / 100

/-- The days of year `y` of a cycle, which ends with February of the next calendar year. -/
def yearLength (y : Int) : Int := if isLeap (y + 1) then 366 else 365

/-- The calendar month of month `mp` of a year that starts March 1, as civilFromDays maps it. -/
def monthOf (mp : Int) : Int := if decide (mp < 10) then mp + 3 else mp - 9

/-- The month of a year that starts March 1 of calendar month `m`, as daysFromCivil maps it. -/
def marchMonth (m : Int) : Int := if m > 2 then m - 3 else m + 9

def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p n && allBelow p n

theorem of_allBelow {p : Nat → Bool} : ∀ {n : Nat}, allBelow p n = true → ∀ i < n, p i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    simp only [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact of_allBelow h.2 i hi
    · exact h.1

/-- Each year of a cycle: yoeOf gives it at its first and last day, and the next year starts after its last day. -/
theorem years : allBelow (fun n =>
    let y : Int := n
    yoeOf (yearStart y) == y && yoeOf (yearStart y + yearLength y - 1) == y &&
      (y == 399 || yearStart (y + 1) == yearStart y + yearLength y)) 400 = true := by decide +kernel

/-- Each day of a year that starts March 1: its month and day, which give the day back. -/
theorem monthsForward : allBelow (fun n => allBelow (fun l =>
    let doy : Int := n
    let leap := l == 1
    let mp := (5 * doy + 2) / 153
    let d := doy - (153 * mp + 2) / 5 + 1
    let m := monthOf mp
    !(decide (doy ≤ 364 + l)) || (decide (1 ≤ m) && decide (m ≤ 12) && decide (1 ≤ d) &&
      decide (d ≤ monthDays (if leap then 4 else 1) m) && (153 * marchMonth m + 2) / 5 + d - 1 == doy &&
      decide (m ≤ 2) == decide (306 ≤ doy))) 2) 366 = true := by decide +kernel

def stepSum (x : Int) : Int := x - x / 1460 + x / 36524 - x / 146096

theorem stepSum_succ (x : Int) (h0 : 0 ≤ x) (h1 : x + 1 ≤ 146096) : stepSum x ≤ stepSum (x + 1) := by
  unfold stepSum; omega

theorem stepSum_mono (a : Int) (ha : 0 ≤ a) : ∀ n : Nat, a + n ≤ 146096 → stepSum a ≤ stepSum (a + n)
  | 0, _ => by simp
  | n + 1, h => by
    have h1 := stepSum_mono a ha n (by omega)
    have h2 := stepSum_succ (a + n) (by omega) (by omega)
    have e : a + ((n + 1 : Nat) : Int) = a + n + 1 := by omega
    rw [e]; omega

theorem yoeOf_mono (a b : Int) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 146096) : yoeOf a ≤ yoeOf b := by
  have := stepSum_mono a ha (b - a).toNat (by omega)
  rw [show a + ((b - a).toNat : Int) = b by omega] at this
  unfold yoeOf; unfold stepSum at this; omega

theorem year_facts (y : Int) (h0 : 0 ≤ y) (h1 : y < 400) :
    yoeOf (yearStart y) = y ∧ yoeOf (yearStart y + yearLength y - 1) = y ∧
      (y = 399 ∨ yearStart (y + 1) = yearStart y + yearLength y) := by
  have h := of_allBelow years y.toNat (by omega)
  rw [Int.toNat_of_nonneg h0] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem yearLength_bounds (y : Int) : 365 ≤ yearLength y ∧ yearLength y ≤ 366 := by
  unfold yearLength; split <;> omega

theorem yearStart_le (a b : Int) (h : a ≤ b) : yearStart a ≤ yearStart b := by
  unfold yearStart; omega

/-- The year of day `doe` of a cycle, and the day within it. -/
theorem yoe_bounds (doe : Int) (h0 : 0 ≤ doe) (h1 : doe ≤ 146096) :
    0 ≤ yoeOf doe ∧ yoeOf doe ≤ 399 ∧ yearStart (yoeOf doe) ≤ doe ∧
      doe ≤ yearStart (yoeOf doe) + yearLength (yoeOf doe) - 1 := by
  have lo := yoeOf_mono 0 doe (by omega) h0 h1
  have hi := yoeOf_mono doe 146096 h0 h1 (by omega)
  have y0 : yoeOf 0 = 0 := by decide
  have y399 : yoeOf 146096 = 399 := by decide
  generalize hy : yoeOf doe = y at lo hi
  refine ⟨by omega, by omega, ?_, ?_⟩
  · by_cases hy0 : y = 0
    · subst hy0; simp [yearStart]; omega
    · have ⟨_, he, hn⟩ := year_facts (y - 1) (by omega) (by omega)
      rw [show y - 1 + 1 = y by omega] at hn
      have hs := yearStart_le y 399 (by omega)
      have hl := yearLength_bounds (y - 1)
      have h399 : yearStart 399 = 145731 := by decide
      rcases hn with hn | hn
      · omega
      · apply Decidable.byContradiction; intro hlt
        have := yoeOf_mono doe (yearStart (y - 1) + yearLength (y - 1) - 1) h0 (by omega) (by omega)
        omega
  · by_cases hy399 : y = 399
    · subst hy399; simp [yearStart, yearLength, isLeap]; omega
    · have ⟨_, _, hn⟩ := year_facts y (by omega) (by omega)
      have ⟨hs', _, _⟩ := year_facts (y + 1) (by omega) (by omega)
      have h0' := yearStart_le 0 (y + 1) (by omega)
      rcases hn with hn | hn
      · omega
      · apply Decidable.byContradiction; intro hlt
        have := yoeOf_mono (yearStart (y + 1)) doe (by simpa [yearStart] using h0') (by omega) h1
        omega

theorem monthDays_leap (y m : Int) : monthDays y m = monthDays (if isLeap y then 4 else 1) m := by
  unfold monthDays; cases isLeap y <;> rfl

theorem isLeap_shift (y k : Int) : isLeap (y + 400 * k) = isLeap y := by
  have h4 : (y + 400 * k) % 4 = y % 4 := by omega
  have h100 : (y + 400 * k) % 100 = y % 100 := by omega
  have h400 : (y + 400 * k) % 400 = y % 400 := by omega
  simp only [isLeap, h4, h100, h400]

theorem forward (doy : Int) (leap : Bool) (h0 : 0 ≤ doy) (h1 : doy ≤ 364 + (if leap then 1 else 0)) :
    let mp := (5 * doy + 2) / 153
    let d := doy - (153 * mp + 2) / 5 + 1
    let m := monthOf mp
    1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ monthDays (if leap then 4 else 1) m ∧ (153 * marchMonth m + 2) / 5 + d - 1 = doy ∧
      (m ≤ 2 ↔ 306 ≤ doy) := by
  have h := of_allBelow (of_allBelow monthsForward doy.toNat (by cases leap <;> simp at h1 <;> omega))
    (if leap then 1 else 0) (by cases leap <;> simp)
  rw [Int.toNat_of_nonneg h0] at h
  cases leap <;> simp_all

theorem civil_eq (z : Int) :
    civilFromDays z =
      let q := (z + 719468) / 146097
      let doe := z + 719468 - q * 146097
      let yoe := yoeOf doe
      let doy := doe - yearStart yoe
      let mp := (5 * doy + 2) / 153
      let m := monthOf mp
      (if decide (m ≤ 2) then yoe + q * 400 + 1 else yoe + q * 400, m, doy - (153 * mp + 2) / 5 + 1) := rfl

theorem days_eq (y m d : Int) :
    daysFromCivil y m d =
      let y' := if m ≤ 2 then y - 1 else y
      y' / 400 * 146097 + yearStart (y' - y' / 400 * 400) + ((153 * marchMonth m + 2) / 5 + d - 1) - 719468 := by
  simp only [daysFromCivil, yearStart, marchMonth]; omega

/-- civilFromDays gives a real date, whose days from civil are the day it came from. -/
theorem civil_valid (z : Int) :
    1 ≤ (civilFromDays z).2.1 ∧ (civilFromDays z).2.1 ≤ 12 ∧ 1 ≤ (civilFromDays z).2.2 ∧
      (civilFromDays z).2.2 ≤ monthDays (civilFromDays z).1 (civilFromDays z).2.1 ∧
      daysFromCivil (civilFromDays z).1 (civilFromDays z).2.1 (civilFromDays z).2.2 = z := by
  rw [civil_eq]
  dsimp only
  generalize hq : (z + 719468) / 146097 = q
  generalize hdoe : z + 719468 - q * 146097 = doe
  have hd0 : 0 ≤ doe := by omega
  have hd1 : doe ≤ 146096 := by omega
  have ⟨y0, y1, ys, ye⟩ := yoe_bounds doe hd0 hd1
  generalize hy : yoeOf doe = yoe at y0 y1 ys ye
  have hl := forward (doe - yearStart yoe) (isLeap (yoe + 1)) (by omega) (by
    unfold yearLength at ye; split at ye <;> rename_i h <;> simp [h] <;> omega)
  dsimp only at hl
  generalize hdoy : doe - yearStart yoe = doy at hl ⊢
  generalize hmp : (5 * doy + 2) / 153 = mp at hl ⊢
  generalize hm : monthOf mp = m at hl ⊢
  obtain ⟨m1, m2, d1, d2, back, feb⟩ := hl
  refine ⟨m1, m2, d1, ?_, ?_⟩
  · rw [monthDays_leap]
    by_cases h2 : m ≤ 2
    · have : isLeap (yoe + q * 400 + 1) = isLeap (yoe + 1) := by
        rw [show yoe + q * 400 + 1 = (yoe + 1) + 400 * q by omega, isLeap_shift]
      simp only [h2, decide_true, ite_true, this]; exact d2
    · have hm2 : m ≠ 2 := by omega
      have e : ∀ a b : Int, monthDays a m = monthDays b m := by
        intro a b; simp only [monthDays, show (m == 2) = false by simp [hm2]]; rfl
      rw [e _ (if isLeap (yoe + 1) then 4 else 1)]; exact d2
  · rw [days_eq]
    dsimp only
    by_cases h2 : m ≤ 2
    · simp only [h2, decide_true, ite_true]
      have e1 : (yoe + q * 400 + 1 - 1) / 400 = q := by omega
      have e2 : yoe + q * 400 + 1 - 1 - q * 400 = yoe := by omega
      rw [e1, e2, back]; omega
    · simp only [h2, decide_false, ite_false, Bool.false_eq_true]
      have e1 : (yoe + q * 400) / 400 = q := by omega
      have e2 : yoe + q * 400 - q * 400 = yoe := by omega
      rw [e1, e2, back]; omega

open Tazuna.Ir.Literal (decimalDigits digitChar digitsFrom decimalDigits_lt digitsFrom_map foldl_decimalDigits)

theorem digitChar_sign (d : Nat) (h : d < 10) : digitChar d ≠ '-' ∧ digitChar d ≠ '+' := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

theorem foldl_zeros (k : Nat) : (List.replicate k 0).foldl (fun a d => a * 10 + d) 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ] using ih

theorem read_padded (w n : Nat) : digitsFrom 10 0 (padded w n) = some n := by
  have hlt : ∀ d ∈ List.replicate (w - (decimalDigits n).length) 0 ++ decimalDigits n, d < 10 := by
    intro d hd
    simp only [List.mem_append, List.mem_replicate] at hd
    rcases hd with ⟨-, rfl⟩ | hd
    · omega
    · exact decimalDigits_lt n d hd
  rw [padded, digitsFrom_map 0 _ hlt, List.foldl_append, foldl_zeros, foldl_decimalDigits]

theorem padded_head (w n : Nat) : ∃ d cs, d < 10 ∧ padded w n = digitChar d :: cs := by
  have hlt : ∀ d ∈ List.replicate (w - (decimalDigits n).length) 0 ++ decimalDigits n, d < 10 := by
    intro d hd
    simp only [List.mem_append, List.mem_replicate] at hd
    rcases hd with ⟨-, rfl⟩ | hd
    · omega
    · exact decimalDigits_lt n d hd
  cases h : List.replicate (w - (decimalDigits n).length) 0 ++ decimalDigits n with
  | nil =>
    have : decimalDigits n ≠ [] := by rw [decimalDigits]; split <;> simp
    simp_all
  | cons d ds => exact ⟨d, ds.map digitChar, hlt d (by simp [h]), by simp [padded, h]⟩

theorem read_year (y : Int) : readYear (yearChars y) = some y := by
  unfold yearChars
  split
  · rename_i hy
    obtain ⟨d, cs, hd, hp⟩ := padded_head 4 y.toNat
    have hs := digitChar_sign d hd
    have hr := read_padded 4 y.toNat
    rw [hp] at hr ⊢
    simp only [readYear, hs.1, hs.2, ite_false, hr, Option.map_some, Int.ofNat_eq_natCast, Option.some.injEq]
    omega
  · split
    · simp only [readYear, ite_true, read_padded, Option.map_some, Int.ofNat_eq_natCast, Option.some.injEq]
      omega
    · simp only [readYear, show ('+' = '-') = False by decide, ite_false, ite_true, read_padded, Option.map_some,
        Int.ofNat_eq_natCast, Option.some.injEq]
      omega

theorem read_two (n : Nat) (h : n < 100) : digitsFrom 10 0 (twoDigits n) = some n := by
  have e := digitsFrom_map 0 [n / 10, n % 10] (by intro d hd; simp at hd; omega)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [twoDigits, e]
  congr 1; omega

/-- Every day has a label, and reading it gives the day back. -/
theorem parse_render (z : Int) : parseDate? (renderDate z) = some z := by
  have hv := civil_valid z
  have hread : readDate (renderDate z).toList = some z := by
    simp only [renderDate]
    generalize hc : civilFromDays z = c at hv
    obtain ⟨y, m, d⟩ := c
    simp only at hv
    obtain ⟨hm1, hm2, hd1, hd2, hdays⟩ := hv
    have hmd : monthDays y m ≤ 31 := by simp only [monthDays]; split <;> (try split) <;> omega
    simp only [String.toList_ofList, readDate, twoDigits, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.reverse_reverse]
    have hm := read_two m.toNat (by omega)
    have hd := read_two d.toNat (by omega)
    simp only [twoDigits] at hm hd
    simp only [read_year, hm, hd, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rw [show (m.toNat : Int) = m by omega, show (d.toNat : Int) = d by omega, hdays]
  simp [parseDate?, hread]

/-- A text that reads as a day is that day's label. -/
theorem render_parse (s : String) (z : Int) (h : parseDate? s = some z) : renderDate z = s := by
  simp only [parseDate?, Option.filter_eq_some_iff, beq_iff_eq] at h
  exact h.2

end Tazuna.Trace.DateThm
