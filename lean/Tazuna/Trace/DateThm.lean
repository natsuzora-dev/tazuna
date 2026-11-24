import Tazuna.Trace.Date

/-!
A date label and its day number are one value written two ways: on years 0000 through 9999, parseDate? and renderDate?
are inverse (`render_parse`, `parse_render`), and a day number has a label exactly from firstDay through lastDay
(`labelled_range`). A trace's dates rest on these: a date is its day number, and its label is what a trace writes.

The calendar repeats every 400 years. Within one cycle, the kernel checks each year's first and last day and each day of
a year that starts March 1 (`years`, `monthsForward`, `monthsBack`), and monotonicity of the year count covers the days
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

/-- Each real date of a year that starts March 1: its day of the year, whose month and day give the date back. -/
theorem monthsBack : allBelow (fun m0 => allBelow (fun d0 => allBelow (fun l =>
    let m : Int := m0 + 1
    let d : Int := d0 + 1
    let doy := (153 * marchMonth m + 2) / 5 + d - 1
    let mp := (5 * doy + 2) / 153
    !(decide (d ≤ monthDays (if l == 1 then 4 else 1) m)) ||
      (decide (0 ≤ doy) && decide (doy ≤ 364 + l) && monthOf mp == m && doy - (153 * mp + 2) / 5 + 1 == d)) 2) 31) 12
    = true := by decide +kernel

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

/-- A day within year `y` of a cycle is in year `y`. -/
theorem yoeOf_within (y doy : Int) (h0 : 0 ≤ y) (h1 : y ≤ 399) (h2 : 0 ≤ doy) (h3 : doy ≤ yearLength y - 1) :
    yoeOf (yearStart y + doy) = y := by
  have ⟨hs, he, _⟩ := year_facts y h0 (by omega)
  have hb : yearStart y + yearLength y - 1 ≤ 146096 := by
    have := yearLength_bounds y
    by_cases hy : y = 399
    · subst hy; simp [yearStart, yearLength, isLeap]
    · have ⟨_, _, hn⟩ := year_facts y h0 (by omega)
      have := yearLength_bounds (y + 1)
      unfold yearStart at hn ⊢; omega
  have hs0 : 0 ≤ yearStart y := by unfold yearStart; omega
  have a := yoeOf_mono (yearStart y) (yearStart y + doy) hs0 (by omega) (by omega)
  have b := yoeOf_mono (yearStart y + doy) (yearStart y + yearLength y - 1) (by omega) (by omega) hb
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

theorem back (m d : Int) (leap : Bool) (hm1 : 1 ≤ m) (hm2 : m ≤ 12) (hd1 : 1 ≤ d)
    (hd2 : d ≤ monthDays (if leap then 4 else 1) m) :
    let doy := (153 * marchMonth m + 2) / 5 + d - 1
    let mp := (5 * doy + 2) / 153
    0 ≤ doy ∧ doy ≤ 364 + (if leap then 1 else 0) ∧ monthOf mp = m ∧ doy - (153 * mp + 2) / 5 + 1 = d := by
  have hmd : monthDays (if leap then 4 else 1) m ≤ 31 := by
    simp only [monthDays]; split <;> (try split) <;> (try split) <;> omega
  have h := of_allBelow (of_allBelow (of_allBelow monthsBack (m - 1).toNat (by omega)) (d - 1).toNat (by omega))
    (if leap then 1 else 0) (by cases leap <;> simp)
  have em : (((m - 1).toNat : Nat) : Int) + 1 = m := by omega
  have ed : (((d - 1).toNat : Nat) : Int) + 1 = d := by omega
  simp only [em, ed] at h
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

/-- A real date is the civil date of its days from civil. -/
theorem days_valid (y m d : Int) (hm1 : 1 ≤ m) (hm2 : m ≤ 12) (hd1 : 1 ≤ d) (hd2 : d ≤ monthDays y m) :
    civilFromDays (daysFromCivil y m d) = (y, m, d) := by
  rw [days_eq]
  dsimp only
  generalize hy' : (if m ≤ 2 then y - 1 else y) = y'
  generalize hq : y' / 400 = q
  generalize hyoe : y' - q * 400 = yoe
  have y0 : 0 ≤ yoe := by omega
  have y1 : yoe ≤ 399 := by omega
  have hleap : monthDays y m = monthDays (if isLeap (yoe + 1) then 4 else 1) m := by
    by_cases h2 : m ≤ 2
    · rw [monthDays_leap]
      have : y = (yoe + 1) + 400 * q := by simp only [h2, ite_true] at hy'; omega
      rw [this, isLeap_shift]
    · have hm2 : m ≠ 2 := by omega
      simp only [monthDays, show (m == 2) = false by simp [hm2], Bool.false_eq_true, ite_false]
  rw [hleap] at hd2
  have hbk := back m d (isLeap (yoe + 1)) hm1 hm2 hd1 hd2
  dsimp only at hbk
  have ⟨b0, b1, bm, bd⟩ := hbk
  generalize hdoy : (153 * marchMonth m + 2) / 5 + d - 1 = doy at b0 b1 bm bd
  have hlen : doy ≤ yearLength yoe - 1 := by
    unfold yearLength; split <;> rename_i h <;> simp [h] at b1 <;> omega
  have hw := yoeOf_within yoe doy y0 y1 b0 hlen
  have hb : yearStart yoe + yearLength yoe - 1 ≤ 146096 := by
    by_cases h : yoe = 399
    · subst h; simp [yearStart, yearLength, isLeap]
    · have ⟨_, _, hn⟩ := year_facts yoe y0 (by omega)
      have := yearStart_le (yoe + 1) 399 (by omega)
      have h399 : yearStart 399 = 145731 := by decide
      have := yearLength_bounds yoe
      omega
  have hs0 : 0 ≤ yearStart yoe := by unfold yearStart; omega
  rw [civil_eq]
  dsimp only
  have e1 : (q * 146097 + yearStart yoe + doy - 719468 + 719468) / 146097 = q := by omega
  have e2 : q * 146097 + yearStart yoe + doy - 719468 + 719468 - q * 146097 = yearStart yoe + doy := by omega
  rw [e1, e2, hw, show yearStart yoe + doy - yearStart yoe = doy by omega, bm, bd]
  simp only [Prod.mk.injEq, and_true]
  by_cases h2 : m ≤ 2
  · simp only [h2, decide_true, ite_true] at hy' ⊢; omega
  · simp only [h2, decide_false, ite_false, Bool.false_eq_true] at hy' ⊢; omega

/-- A day number has a label exactly from 0000-01-01 through 9999-12-31. -/
theorem civil_year_range (z : Int) :
    (0 ≤ (civilFromDays z).1 ∧ (civilFromDays z).1 ≤ 9999) ↔ (firstDay ≤ z ∧ z ≤ lastDay) := by
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
  obtain ⟨-, -, -, -, -, feb⟩ := hl
  have h399 : yearStart 399 = 145731 := by decide
  have hlast : (yoe = 399 ∧ 306 ≤ doy) ↔ 146037 ≤ doe := by
    constructor
    · intro ⟨a, b⟩; subst a; omega
    · intro h
      have : yoe = 399 := by
        apply Decidable.byContradiction; intro hne
        have ⟨_, _, hn⟩ := year_facts yoe y0 (by omega)
        have := yearStart_le (yoe + 1) 399 (by omega)
        have := yearLength_bounds yoe
        omega
      exact ⟨this, by subst this; omega⟩
  simp only [firstDay, lastDay]
  by_cases h2 : m ≤ 2
  · simp only [h2, decide_true, ite_true]; omega
  · simp only [h2, decide_false, ite_false, Bool.false_eq_true]; omega

theorem digitChar_toList (n : Int) : (digitChar n).toList = [Char.ofNat (48 + n % 10).toNat] := by
  simp [digitChar]

theorem digitChar_toNat (n : Int) : ((Char.ofNat (48 + n % 10).toNat).toNat : Int) = 48 + n % 10 := by
  have h0 : 0 ≤ n % 10 := Int.emod_nonneg _ (by decide)
  have h1 : n % 10 < 10 := Int.emod_lt_of_pos _ (by decide)
  have : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 3 ∨ n % 10 = 4 ∨ n % 10 = 5 ∨ n % 10 = 6 ∨ n % 10 = 7 ∨
    n % 10 = 8 ∨ n % 10 = 9 := by omega
  rcases this with h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl

theorem dateLabel_toList (y m d : Int) : (dateLabel y m d).toList =
    [Char.ofNat (48 + y / 1000 % 10).toNat, Char.ofNat (48 + y / 100 % 10).toNat, Char.ofNat (48 + y / 10 % 10).toNat,
      Char.ofNat (48 + y % 10).toNat, '-', Char.ofNat (48 + m / 10 % 10).toNat, Char.ofNat (48 + m % 10).toNat, '-',
      Char.ofNat (48 + d / 10 % 10).toNat, Char.ofNat (48 + d % 10).toNat] := by
  simp [dateLabel, String.toList_append, digitChar_toList]

/-- The digits of a label give back its year, month and day, and the label is a date label when the day is real. -/
theorem label_parts (y m d : Int) (hy0 : 0 ≤ y) (hy1 : y ≤ 9999) (hm1 : 1 ≤ m) (hm2 : m ≤ 12) (hd1 : 1 ≤ d)
    (hd2 : d ≤ monthDays y m) :
    labelYear (dateLabel y m d) = y ∧ labelMonth (dateLabel y m d) = m ∧ labelDay (dateLabel y m d) = d ∧
      isDateLabel (dateLabel y m d) = true := by
  have hmd : monthDays y m ≤ 31 := by simp only [monthDays]; split <;> (try split) <;> omega
  have hdig : ∀ i, i < 10 → i ≠ 4 → i ≠ 7 → 0 ≤ digitAt (dateLabel y m d) i ∧ digitAt (dateLabel y m d) i ≤ 9 := by
    intro i hi h4 h7
    simp only [digitAt, codeAt, dateLabel_toList]
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 8 ∨ i = 9 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some,
        digitChar_toNat] <;> omega
  have hd : ∀ (n : Int), (Char.ofNat (48 + n % 10).toNat).toNat - (48 : Int) = n % 10 := by
    intro n; rw [digitChar_toNat]; omega
  have hY : labelYear (dateLabel y m d) = y := by
    simp only [labelYear, digitAt, codeAt, dateLabel_toList, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.map_some, Option.getD_some, hd]
    omega
  have hM : labelMonth (dateLabel y m d) = m := by
    simp only [labelMonth, digitAt, codeAt, dateLabel_toList, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.map_some, Option.getD_some, hd]
    omega
  have hD : labelDay (dateLabel y m d) = d := by
    simp only [labelDay, digitAt, codeAt, dateLabel_toList, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.map_some, Option.getD_some, hd]
    omega
  refine ⟨hY, hM, hD, ?_⟩
  have hlen : (dateLabel y m d).length = 10 := by rw [← String.length_toList, dateLabel_toList]; rfl
  have h4 : codeAt (dateLabel y m d) 4 = 45 := by simp only [codeAt, dateLabel_toList]; rfl
  have h7 : codeAt (dateLabel y m d) 7 = 45 := by simp only [codeAt, dateLabel_toList]; rfl
  simp only [isDateLabel, isDigitAt, hlen, h4, h7, hY, hM, hD, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  have := hdig 0; have := hdig 1; have := hdig 2; have := hdig 3; have := hdig 5; have := hdig 6; have := hdig 8
  have := hdig 9
  simp_all

/-- A date label is the label of its own year, month and day, a year from 0000 through 9999. -/
theorem label_of_parts (s : String) (h : isDateLabel s = true) :
    dateLabel (labelYear s) (labelMonth s) (labelDay s) = s ∧ 0 ≤ labelYear s ∧ labelYear s ≤ 9999 := by
  simp only [isDateLabel, isDigitAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlen, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, -⟩, -⟩, -⟩, -⟩ := h
  rw [← String.length_toList] at hlen
  match hs : s.toList, hlen with
  | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9], _ =>
    simp only [digitAt, codeAt, hs, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some,
      Option.getD_some] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
    have hY : labelYear s = (c0.toNat - 48) * 1000 + (c1.toNat - 48) * 100 + (c2.toNat - 48) * 10 + (c3.toNat - 48) := by
      simp [labelYear, digitAt, codeAt, hs]
    have hM : labelMonth s = (c5.toNat - 48) * 10 + (c6.toNat - 48) := by simp [labelMonth, digitAt, codeAt, hs]
    have hD : labelDay s = (c8.toNat - 48) * 10 + (c9.toNat - 48) := by simp [labelDay, digitAt, codeAt, hs]
    have hc : ∀ (c : Char) (n : Int), (c.toNat : Int) - 48 = n % 10 → Char.ofNat (48 + n % 10).toNat = c := by
      intro c n hn
      have : (48 + n % 10).toNat = c.toNat := by omega
      rw [this, Char.ofNat_toNat]
    refine ⟨String.ext ?_, by omega, by omega⟩
    rw [dateLabel_toList, hs, hY, hM, hD]
    have e4 : c4 = '-' := by
      apply Char.ext; apply UInt32.toNat_inj.mp; show c4.toNat = 45; omega
    have e7 : c7 = '-' := by
      apply Char.ext; apply UInt32.toNat_inj.mp; show c7.toNat = 45; omega
    rw [e4, e7]
    simp only [List.cons.injEq, and_true]
    refine ⟨hc _ _ ?_, hc _ _ ?_, hc _ _ ?_, hc _ _ ?_, trivial, hc _ _ ?_, hc _ _ ?_, trivial, hc _ _ ?_, hc _ _ ?_⟩ <;>
      omega

/-- Rendering a day number and parsing the label gives the day number back. -/
theorem parse_render (z : Int) (s : String) (h : renderDate? z = some s) : parseDate? s = some z := by
  simp only [renderDate?] at h
  have hv := civil_valid z
  generalize hc : civilFromDays z = c at h hv
  obtain ⟨y, m, d⟩ := c
  simp only at h hv
  obtain ⟨hm1, hm2, hd1, hd2, hdays⟩ := hv
  split at h
  · rename_i hy
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hy
    cases h
    obtain ⟨hY, hM, hD, hl⟩ := label_parts y m d hy.1 hy.2 hm1 hm2 hd1 hd2
    simp only [parseDate?, hl, ite_true, hY, hM, hD, hdays]
  · cases h

/-- Parsing a date label and rendering the day number gives the label back. -/
theorem render_parse (s : String) (z : Int) (h : parseDate? s = some z) : renderDate? z = some s := by
  simp only [parseDate?] at h
  split at h
  · rename_i hl
    cases h
    obtain ⟨hs, hy0, hy1⟩ := label_of_parts s hl
    simp only [isDateLabel, Bool.and_eq_true, decide_eq_true_eq] at hl
    have hdv := days_valid (labelYear s) (labelMonth s) (labelDay s) hl.1.1.1.2 hl.1.1.2 hl.1.2 hl.2
    simp only [renderDate?, hdv, hy0, hy1, decide_true, Bool.and_self, ite_true, hs]
  · cases h

/-- A day number has a label exactly from 0000-01-01 through 9999-12-31. -/
theorem labelled_range (z : Int) : (renderDate? z).isSome = (decide (firstDay ≤ z) && decide (z ≤ lastDay)) := by
  have h := civil_year_range z
  simp only [renderDate?]
  generalize civilFromDays z = c at h
  obtain ⟨y, m, d⟩ := c
  have e : (decide (0 ≤ y) && decide (y ≤ 9999)) = (decide (firstDay ≤ z) && decide (z ≤ lastDay)) := by
    rw [← Bool.decide_and, ← Bool.decide_and]; exact decide_eq_decide.mpr h
  rw [← e]
  split <;> rename_i hb <;> simp [hb]

end Tazuna.Trace.DateThm
