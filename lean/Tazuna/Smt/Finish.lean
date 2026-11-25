import Tazuna.Smt.Events

/-! Pieces of the steps that apply events: a subscription's wrap of the received value into an event, and the service's
invariants on a records term. `Tazuna.Smt.StepEnd` composes them with the events loop and the cascade. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable (L : Layout)

/-- The event a subscription wraps the received value into, with its condition. -/
def encodeWrap {v : ServiceV} {i : Fin v.subscribes.length} (ec : EventCode v i) (value : Term) :
    Except Refusal (Term × Term) := do
  let vc ← need "a value that has no term" (Code.ofTerm? _ value)
  let (ev, c) ← ec.wrap (vc, ())
  let et ← need "an event that has no term" (Code.term? _ ev)
  pure (et, c)

/-- The service's invariants on the records term: each rule's name and whether it holds, with the condition. -/
def encodeInvariants {r : Ty} (inv : Code (Ty.fn [r] Ty.rules)) (records : Term) :
    Except Refusal (List (Term × Term) × Term) := do
  let rc ← need "records that have no term" (Code.ofTerm? r records)
  let (invs, c) ← inv (rc, ())
  let rules ← ruleTerms L invs
  pure (rules, c)

end

section
variable {L : Layout} {T : List TypeDecl} {M : Model}

theorem wrap_rel {v : ServiceV} (i : Fin v.subscribes.length) (value : (v.subscribes.get i).event.den0)
    (hd : EventData v i) {ec : EventCode v i} (he : ec.Rel M L hd) {sv : Term}
    (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M)) {et c : Term} (henc : encodeWrap ec sv = .ok (et, c))
    (hc : Holds M c) : RelV L v.event (Ty.up _ hd.event ((v.subscribes.get i).wrap.fn (value, ()))) (et.denote M) := by
  obtain ⟨vc, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ev, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨et', h3, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hvc : Smt.Rel M L _ (Ty.up _ hd.value value) vc := (rel_ofTerm (need_ok.1 h1) _).2 hsv
  have hev := he.wrap _ (vc, ()) (rels1 hd.value hd.wrapArgs hvc) ev c h2 hc
  erw [Ty.up_fn _ _ _ hd.wrapArgs hd.event] at hev
  exact (rel_term (need_ok.1 h3) _).1 hev

/-- The wrap's condition is exact: it holds exactly when the wrap fits at the value. -/
theorem wrap_exact {v : ServiceV} (i : Fin v.subscribes.length) (value : (v.subscribes.get i).event.den0)
    (hd : EventData v i) {ec : EventCode v i} {ce : Term} (hec : EventCode.of L v i = .ok (ec, ce)) (hce : Holds M ce)
    {sv : Term} (hsv : RelV L _ (Ty.up _ hd.value value) (sv.denote M)) {et c : Term}
    (henc : encodeWrap ec sv = .ok (et, c)) :
    Holds M c ↔ (v.subscribes.get i).wrap.appFits L.count (value, ()) := by
  obtain ⟨⟨a, c1'⟩, -, hec'⟩ := bind_ok.1 hec
  obtain ⟨⟨w, c2'⟩, g2, hec'⟩ := bind_ok.1 hec'
  obtain ⟨⟨n, c3'⟩, -, hec'⟩ := bind_ok.1 hec'
  cases pure_ok.1 hec'
  obtain ⟨-, hcwn⟩ := (holds_andT _ _).1 hce
  obtain ⟨hcw, -⟩ := (holds_andT _ _).1 hcwn
  obtain ⟨vc, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨ev, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨et', -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hvc : Smt.Rel M L _ (Ty.up _ hd.value value) vc := (rel_ofTerm (need_ok.1 h1) _).2 hsv
  exact (v.subscribes.get i).wrap.app_exact g2 hcw (by simpa using ofTerm_notFn (need_ok.1 h1)) _ _
    (rels1 hd.value hd.wrapArgs hvc) h2

/-- The invariant terms name the rules the records break. -/
theorem invariants_rel {r : Ty} (f : Fun (Ty.fn [r] Ty.rules)) (hr : r.isData = true) (hf : (Ty.fn [r] Ty.rules).isData = true)
    {inv : Code (Ty.fn [r] Ty.rules)} (hinv : Smt.Rel M L _ (Ty.up _ hf f.fn) inv) (recs : r.den0) {records : Term}
    (hrec : RelV L r (Ty.up _ hr recs) (records.denote M)) {rules : List (Term × Term)} {c : Term}
    (henc : encodeInvariants L inv records = .ok (rules, c)) (hc : Holds M c) :
    brokenIn M rules = Step.broken (f.fn (recs, ())) := by
  obtain ⟨rc, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨invs, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨rules', h3, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hrc : Smt.Rel M L r (Ty.up _ hr recs) rc := (rel_ofTerm (need_ok.1 h1) _).2 hrec
  have hargs : (Ty.tuple [r]).isData = true := by simp [Ty.isData, Ty.isDatas, hr]
  have hiv := hinv _ _ (rels1 hr hargs hrc) invs c h2 hc
  erw [Ty.up_fn _ Ty.rules _ hargs rfl] at hiv
  exact rules_broken h3 _ hiv

/-- The invariants' condition is exact: it holds exactly when they fit at the records. -/
theorem invariants_exact {r : Ty} (f : Fun (Ty.fn [r] Ty.rules)) (hr : r.isData = true)
    {inv : Code (Ty.fn [r] Ty.rules)} {ci : Term} (hf : f.code L = .ok (inv, ci)) (hci : Holds M ci) (recs : r.den0)
    {records : Term} (hrec : RelV L r (Ty.up _ hr recs) (records.denote M)) {rules : List (Term × Term)} {c : Term}
    (henc : encodeInvariants L inv records = .ok (rules, c)) :
    Holds M c ↔ f.appFits L.count (recs, ()) := by
  obtain ⟨rc, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨invs, c1⟩, h2, henc⟩ := bind_ok.1 henc
  obtain ⟨rules', -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hrc : Smt.Rel M L r (Ty.up _ hr recs) rc := (rel_ofTerm (need_ok.1 h1) _).2 hrec
  exact f.app_exact hf hci (by simpa using ofTerm_notFn (need_ok.1 h1)) _ _ (rels1 hr f.args_data hrc) h2

end

end Tazuna.Smt
