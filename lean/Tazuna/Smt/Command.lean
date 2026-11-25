import Tazuna.Smt.EncodeExact

/-! A command's codes and the facts its data types give, which the step's command and an own command's internal step
share. -/

namespace Tazuna.Smt

open Tazuna.Ir

/-- The codes of a command's functions. -/
structure CommandCode {r e c : Ty} (x : CommandV r e c) where
  accepts : Code (Ty.fn [x.input] Ty.rules)
  decide : Code (Ty.fn [Ty.ctx r x.input c] (Ty.result (.list e) x.rejection))
  ensures : Code (Ty.fn [Ty.ctx r x.input c, r] Ty.rules)

/-- A command's types are data, as the `command` built-in demands of its type arguments. -/
structure CommandData {r e c : Ty} (x : CommandV r e c) : Prop where
  records : r.isData = true
  event : e.isData = true
  caller : c.isData = true
  input : x.input.isData = true
  rejection : x.rejection.isData = true

/-- A command's types are data, since its `decide` is. -/
theorem _root_.Tazuna.Ir.CommandV.data {r e c : Ty} (x : CommandV r e c) : CommandData x := by
  have h := x.decide.ht
  simp only [Ty.ctx, Ty.result, Ty.isData, Ty.isDatas, Ty.isDatass, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.2.1.1, h.1.1.1.2.2.1, h.1.1.1.2.1, h.2.2.1.1⟩

section
variable {r e c : Ty} {x : CommandV r e c} (hd : CommandData x)
include hd

theorem CommandData.accepts : (Ty.fn [x.input] Ty.rules).isData = true := by
  simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hd.input]
theorem CommandData.ctx : (Ty.ctx r x.input c).isData = true := by
  simp [Ty.ctx, Ty.isData, Ty.isDatas, Ty.isDatass, hd.records, hd.input, hd.caller]
theorem CommandData.ctxArgs : (Ty.tuple [Ty.ctx r x.input c]).isData = true := by
  simp [Ty.isData, Ty.isDatas, hd.ctx]
theorem CommandData.events : (Ty.list e).isData = true := by simp [Ty.isData, hd.event]
theorem CommandData.result : (Ty.result (.list e) x.rejection).isData = true := by
  simp [Ty.result, Ty.isData, Ty.isDatas, Ty.isDatass, hd.event, hd.rejection]
theorem CommandData.decide : (Ty.fn [Ty.ctx r x.input c] (Ty.result (.list e) x.rejection)).isData = true := by
  simp only [Ty.isData, Ty.isDatas, hd.ctx, hd.result, Bool.and_self]
theorem CommandData.ensures : (Ty.fn [Ty.ctx r x.input c, r] Ty.rules).isData = true := by
  simp [Ty.isData, Ty.isDatas, Ty.isDatass, Ty.rules, Ty.bool, hd.ctx, hd.records]
theorem CommandData.ensArgs : (Ty.tuple [Ty.ctx r x.input c, r]).isData = true := by
  simp [Ty.isData, Ty.isDatas, hd.ctx, hd.records]

end

/-- The codes relate to the command's functions in the model. -/
structure CommandCode.Rel (M : Model) (L : Layout) {r e c : Ty} {x : CommandV r e c}
    (cc : CommandCode x) : Prop where
  accepts : Smt.Rel M L _ (Ty.up _ x.data.accepts x.accepts.fn) cc.accepts
  decide : Smt.Rel M L _ (Ty.up _ x.data.decide x.decide.fn) cc.decide
  ensures : Smt.Rel M L _ (Ty.up _ x.data.ensures x.ensures.fn) cc.ensures

/-- A command's codes, from the sources it keeps, with their condition. -/
def CommandCode.of (L : Layout) {r e c : Ty} (x : CommandV r e c) : Except Refusal (CommandCode x × Term) := do
  let (a, c1) ← x.accepts.code L
  let (d, c2) ← x.decide.code L
  let (n, c3) ← x.ensures.code L
  pure (⟨a, d, n⟩, andT c1 (andT c2 c3))

theorem CommandCode.rel_of {M : Model} {L : Layout} {r e c : Ty} {x : CommandV r e c}
    {cc : CommandCode x} {cx : Term} (h : CommandCode.of L x = .ok (cc, cx)) (hc : Holds M cx) : cc.Rel M L := by
  obtain ⟨⟨a, c1⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨⟨d, c2⟩, h2, h⟩ := bind_ok.1 h
  obtain ⟨⟨n, c3⟩, h3, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  have hc := (holds_andT _ _).1 hc
  have hc' := (holds_andT _ _).1 hc.2
  exact ⟨x.accepts.code_fn _ h1 hc.1, x.decide.code_fn _ h2 hc'.1, x.ensures.code_fn _ h3 hc'.2⟩

section
variable {M : Model} {L : Layout}

/-- A command's codes' own condition is exact: it holds exactly when its three kept sources fit. -/
theorem commandCode_exact {r e c : Ty} {x : CommandV r e c} {cc : CommandCode x} {cx : Term}
    (h : CommandCode.of L x = .ok (cc, cx)) :
    Holds M cx ↔ (x.accepts.fits L.count).1 ∧ (x.decide.fits L.count).1 ∧ (x.ensures.fits L.count).1 := by
  obtain ⟨⟨a, c1⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨⟨d, c2⟩, h2, h⟩ := bind_ok.1 h
  obtain ⟨⟨n, c3⟩, h3, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  rw [holds_andT, holds_andT, (x.accepts.code_exact (M := M) h1).1, (x.decide.code_exact (M := M) h2).1,
    (x.ensures.code_exact (M := M) h3).1]

end

end Tazuna.Smt
