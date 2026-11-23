import Tazuna.Smt.Date
import Tazuna.Thm.Data.Time
import Tazuna.Thm.Guarantee

/-!
The date terms denote what Data.Time computes: a term of a string is a date label exactly when isDateLabel holds of the
string, and then names its day number; the label term of a day number is dateLabel of civilFromDays.
-/

namespace Tazuna.Thm.Smt.Date

open Tazuna.Data Tazuna.Smt

variable (M : Model)

@[simp] theorem toInt_int (n : Int) : (Lit.int n).toInt = n := rfl
@[simp] theorem toStr_str (s : String) : (Lit.str s).toStr = s := rfl
@[simp] theorem toBool_bool (b : Bool) : (Lit.bool b).toBool = b := rfl


theorem codeAtT_denote (t : Term) (i : Nat) : (codeAtT t i).denote M = .int (codeAt (t.denote M).toStr i) := by
  simp only [codeAtT, intT, Term.denote, toInt_int, toStr_str]
  generalize (t.denote M).toStr = s
  cases h : s.toList[i]? <;> simp [codeAt, h]

theorem digitAtT_denote (t : Term) (i : Nat) : (digitAtT t i).denote M = .int (digitAt (t.denote M).toStr i) := by
  simp only [digitAtT, Term.denote, codeAtT_denote, intT, toInt_int, digitAt]

theorem toInt_denote_digitAt (t : Term) (i : Nat) :
    ((digitAtT t i).denote M).toInt = digitAt (t.denote M).toStr i := by
  rw [digitAtT_denote]; rfl

theorem labelYearT_denote (t : Term) : (labelYearT t).denote M = .int (labelYear (t.denote M).toStr) := by
  simp only [labelYearT, Term.denote, toInt_denote_digitAt, intT, toInt_int, labelYear]

theorem labelMonthT_denote (t : Term) : (labelMonthT t).denote M = .int (labelMonth (t.denote M).toStr) := by
  simp only [labelMonthT, Term.denote, toInt_denote_digitAt, intT, toInt_int, labelMonth]

theorem labelDayT_denote (t : Term) : (labelDayT t).denote M = .int (labelDay (t.denote M).toStr) := by
  simp only [labelDayT, Term.denote, toInt_denote_digitAt, intT, toInt_int, labelDay]

theorem isLeapT_holds (y : Term) : (isLeapT y).holds M = isLeap (y.denote M).toInt := by
  simp [isLeapT, isLeap, Term.holds, Term.denote, intT, bne, Bool.beq_eq_decide_eq]

theorem monthDaysT_denote (y m : Term) (yi mi : Int) (hy : y.denote M = .int yi) (hm : m.denote M = .int mi) :
    (monthDaysT y m).denote M = .int (monthDays yi mi) := by
  have hl := isLeapT_holds M y
  simp only [Term.holds, hy, toInt_int] at hl
  simp only [monthDaysT, monthDays, Term.denote, intT, toBool_bool, hl, hm]
  by_cases h2 : mi = 2
  · subst h2; cases isLeap yi <;> simp
  · by_cases h4 : mi = 4 <;> by_cases h6 : mi = 6 <;> by_cases h9 : mi = 9 <;> by_cases h11 : mi = 11 <;> simp_all

theorem dateValidT_holds (t : Term) : (dateValidT t).holds M = isDateLabel (t.denote M).toStr := by
  have hy := labelYearT_denote M t
  have hm := labelMonthT_denote M t
  have hd := labelDayT_denote M t
  have hc4 := codeAtT_denote M t 4
  have hc7 := codeAtT_denote M t 7
  simp only [dateValidT, List.foldl, Term.holds, Term.denote, isDigitAtT, toInt_denote_digitAt, hy, hm, hd, hc4, hc7,
    monthDaysT_denote, intT, toBool_bool, toInt_int, isDateLabel, isDigitAt, Lit.int.injEq, String.length]
  simp only [Bool.and_assoc, Bool.beq_eq_decide_eq]
  congr 1
  exact decide_eq_decide.mpr (by omega)

theorem daysFromCivilT_denote (y m d : Term) :
    (daysFromCivilT y m d).denote M = .int (daysFromCivil (y.denote M).toInt (m.denote M).toInt (d.denote M).toInt) := by
  simp only [daysFromCivilT, daysFromCivil, Term.denote, intT, toBool_bool, toInt_int]
  by_cases h : (m.denote M).toInt ≤ 2
  · have h' : ¬ (2 < (m.denote M).toInt) := by omega
    simp [h, h']
  · have h' : 2 < (m.denote M).toInt := by omega
    simp [h, h']

theorem dayT_denote (t : Term) :
    (dayT t).denote M = .int (daysFromCivil (labelYear (t.denote M).toStr) (labelMonth (t.denote M).toStr)
      (labelDay (t.denote M).toStr)) := by
  rw [dayT, daysFromCivilT_denote, labelYearT_denote, labelMonthT_denote, labelDayT_denote]; rfl

theorem monthOfT_denote (mp : Term) :
    (monthOfT mp).denote M =
      .int (if decide ((mp.denote M).toInt < 10) then (mp.denote M).toInt + 3 else (mp.denote M).toInt - 9) := by
  simp only [monthOfT, Term.denote, intT, toInt_int, toBool_bool]
  by_cases h : (mp.denote M).toInt < 10 <;> simp [h]

theorem yearOfT_denote (m base : Term) :
    (yearOfT m base).denote M =
      .int (if decide ((m.denote M).toInt ≤ 2) then (base.denote M).toInt + 1 else (base.denote M).toInt) := by
  simp only [yearOfT, Term.denote, intT, toInt_int, toBool_bool]
  by_cases h : (m.denote M).toInt ≤ 2 <;> simp [h]

theorem civilT_denote (z : Term) :
    (((civilT z).1.denote M).toInt, ((civilT z).2.1.denote M).toInt, ((civilT z).2.2.denote M).toInt) =
      civilFromDays (z.denote M).toInt := by
  simp only [civilT, civilFromDays, monthOfT_denote, yearOfT_denote, Term.denote, intT, toInt_int]
  rfl

theorem digitCharT_denote (n : Term) : (digitCharT n).denote M = .str (digitChar (n.denote M).toInt) := by
  simp only [digitCharT, Term.denote, intT, toInt_int, digitChar]
  have h0 : 0 ≤ (n.denote M).toInt % 10 := Int.emod_nonneg _ (by decide)
  have h1 : (n.denote M).toInt % 10 < 10 := Int.emod_lt_of_pos _ (by decide)
  have : 0 ≤ 48 + (n.denote M).toInt % 10 ∧ 48 + (n.denote M).toInt % 10 ≤ 0x2FFFF := ⟨by omega, by omega⟩
  simp [this]

theorem labelT_denote (z : Term) :
    (labelT z).denote M = .str (let (y, m, d) := civilFromDays (z.denote M).toInt; dateLabel y m d) := by
  rw [← civilT_denote]
  simp only [labelT, Term.denote, digitCharT_denote, intT, toInt_int, toStr_str, dateLabel]

theorem inRangeT_holds (z : Term) : (inRangeT z).holds M = (renderDate? (z.denote M).toInt).isSome := by
  rw [Tazuna.Thm.Data.Time.labelled_range]
  simp only [inRangeT, Term.holds, Term.denote, intT, toInt_int, toBool_bool]
  rfl

/-- The body that the script gives `date_label` denotes what `Term.dateLabel` denotes. -/
@[guarantee] theorem dateLabelBody_denote (z : Term) : (dateLabelBody z).denote M = (Term.dateLabel z).denote M := by
  have h := inRangeT_holds M z
  simp only [Term.holds] at h
  simp only [dateLabelBody, Term.denote, h, labelT_denote, renderDate?]
  generalize civilFromDays (z.denote M).toInt = c
  obtain ⟨y, m, d⟩ := c
  by_cases hy : (decide (0 ≤ y) && decide (y ≤ 9999)) = true <;> simp [hy]

end Tazuna.Thm.Smt.Date
