import Tazuna.Smt.Term

/-!
The terms of a date label: whether a string is a label `YYYY-MM-DD` of a real day, the day number it names, and the label
of a day number. Each mirrors the definition in Ir.Time that eval runs (isDateLabel, daysFromCivil, civilFromDays,
dateLabel), operation by operation. A date that the encoding makes, such as a record's date field or an addDays result,
is the label of a day number (`Term.dateLabel`), whose day number the encoding reads without parsing; these terms read a
label that arrives as a string.
-/

namespace Tazuna.Smt

open Tazuna.Ir Tazuna.Semantics

def intT (n : Int) : Term := .lit (.int n)

def codeAtT (s : Term) (i : Nat) : Term := .toCode (.strAt s (intT i))

def digitAtT (s : Term) (i : Nat) : Term := .sub (codeAtT s i) (intT 48)

def isDigitAtT (s : Term) (i : Nat) : Term := .and (.le (intT 0) (digitAtT s i)) (.le (digitAtT s i) (intT 9))

def isLeapT (y : Term) : Term :=
  .and (.eq (.mod y (intT 4)) (intT 0)) (.or (.not (.eq (.mod y (intT 100)) (intT 0))) (.eq (.mod y (intT 400)) (intT 0)))

def monthDaysT (y m : Term) : Term :=
  .ite (.eq m (intT 2)) (.ite (isLeapT y) (intT 29) (intT 28))
    (.ite (.or (.or (.or (.eq m (intT 4)) (.eq m (intT 6))) (.eq m (intT 9))) (.eq m (intT 11))) (intT 30) (intT 31))

def labelYearT (s : Term) : Term :=
  .add (.add (.add (.mul (digitAtT s 0) (intT 1000)) (.mul (digitAtT s 1) (intT 100))) (.mul (digitAtT s 2) (intT 10)))
    (digitAtT s 3)

def labelMonthT (s : Term) : Term := .add (.mul (digitAtT s 5) (intT 10)) (digitAtT s 6)

def labelDayT (s : Term) : Term := .add (.mul (digitAtT s 8) (intT 10)) (digitAtT s 9)

/-- That the string `s` is a date label (isDateLabel). -/
def dateValidT (s : Term) : Term :=
  [isDigitAtT s 0, isDigitAtT s 1, isDigitAtT s 2, isDigitAtT s 3, .eq (codeAtT s 4) (intT 45), isDigitAtT s 5,
    isDigitAtT s 6, .eq (codeAtT s 7) (intT 45), isDigitAtT s 8, isDigitAtT s 9, .le (intT 1) (labelMonthT s),
    .le (labelMonthT s) (intT 12), .le (intT 1) (labelDayT s), .le (labelDayT s) (monthDaysT (labelYearT s) (labelMonthT s))
  ].foldl .and (.eq (.len s) (intT 10))

/-- daysFromCivil of the terms `y`, `m` and `d`. -/
def daysFromCivilT (y m d : Term) : Term :=
  let y := Term.ite (.le m (intT 2)) (.sub y (intT 1)) y
  let era := Term.div y (intT 400)
  let yoe := Term.sub y (.mul era (intT 400))
  let doy := Term.sub (.add (.div (.add (.mul (intT 153)
    (.ite (.lt (intT 2) m) (.sub m (intT 3)) (.add m (intT 9)))) (intT 2)) (intT 5)) d) (intT 1)
  let doe := Term.add (.sub (.add (.mul yoe (intT 365)) (.div yoe (intT 4))) (.div yoe (intT 100))) doy
  .sub (.add (.mul era (intT 146097)) doe) (intT 719468)

/-- The day number of the date label `s`, when it is one (parseDate?). -/
def dayT (s : Term) : Term := daysFromCivilT (labelYearT s) (labelMonthT s) (labelDayT s)

/-- The month of civilFromDays from its `mp`. -/
def monthOfT (mp : Term) : Term := .ite (.lt mp (intT 10)) (.add mp (intT 3)) (.sub mp (intT 9))

/-- The year of civilFromDays from its month and `yoe + era * 400`; both branches add, so both are integers. -/
def yearOfT (m base : Term) : Term := .ite (.le m (intT 2)) (.add base (intT 1)) (.add base (intT 0))

/-- civilFromDays of the term `z`: its year, month and day. -/
def civilT (z : Term) : Term × Term × Term :=
  let z := Term.add z (intT 719468)
  let era := Term.div z (intT 146097)
  let doe := Term.sub z (.mul era (intT 146097))
  let yoe := Term.div (.sub (.add (.sub doe (.div doe (intT 1460))) (.div doe (intT 36524))) (.div doe (intT 146096)))
    (intT 365)
  let doy := Term.sub doe (.sub (.add (.mul (intT 365) yoe) (.div yoe (intT 4))) (.div yoe (intT 100)))
  let mp := Term.div (.add (.mul (intT 5) doy) (intT 2)) (intT 153)
  let d := Term.add (.sub doy (.div (.add (.mul (intT 153) mp) (intT 2)) (intT 5))) (intT 1)
  let m := monthOfT mp
  (yearOfT m (.add yoe (.mul era (intT 400))), m, d)

def digitCharT (n : Term) : Term := .fromCode (.add (intT 48) (.mod n (intT 10)))

/-- The label of the day number `z` (dateLabel of civilFromDays). -/
def labelT (z : Term) : Term :=
  let (y, m, d) := civilT z
  let dash : Term := .lit (.str "-")
  .strCat (.strCat (.strCat (.strCat (.strCat (.strCat (.strCat (.strCat (.strCat
    (digitCharT (.div y (intT 1000))) (digitCharT (.div y (intT 100)))) (digitCharT (.div y (intT 10))))
    (digitCharT y)) dash) (digitCharT (.div m (intT 10)))) (digitCharT m)) dash) (digitCharT (.div d (intT 10))))
    (digitCharT d)

/-- That the day number `z` has a label: it is 0000-01-01 through 9999-12-31 (renderDate?). -/
def inRangeT (z : Term) : Term := .and (.le (intT firstDay) z) (.le z (intT lastDay))

/-- What the script defines `date_label` of the day number `z` as: its label, or the empty string when it has none. -/
def dateLabelBody (z : Term) : Term := .ite (inRangeT z) (labelT z) (.lit (.str ""))

end Tazuna.Smt
