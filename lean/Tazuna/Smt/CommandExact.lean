import Tazuna.Smt.EventExact
import Tazuna.Smt.AnswerStep

/-! What the exactness theorems of the steps share: conditions under `ite`, argument tuples' relations, the exactness of
a command's codes, and what a query's `ensures` asks to fit. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {M : Model} {L : Layout}

theorem holds_ite_tt {c a : Term} {b : Bool} (h : (c.denote M).toBool = b) : Holds M (.ite c a tt) ↔ (b = true → Holds M a) := by
  rw [holds_ite, h]; cases b <;> simp [holds_tt]

theorem up_app2 {r e : Ty} (hr : r.isData = true) (he : e.isData = true) (h : (Ty.fn [r, e] r).isData = true)
    (g : (Ty.fn [r, e] r).den0) (x : r.den0) (ev : e.den0) :
    (Ty.up _ h g) (Ty.up r hr x, Ty.up e he ev, ()) = Ty.up r hr (g (x, ev, ())) := by
  have hargs : (Ty.tuple [r, e]).isData = true := by simp [Ty.isData, Ty.isDatas, hr, he]
  have := Ty.up_fn [r, e] r h hargs hr g (x, ev, ())
  erw [Ty.up_tuple _ _ _ hr (by simp [Ty.isData, Ty.isDatas, he]), Ty.up_tuple _ _ _ he rfl] at this
  exact this

theorem rels2 {a b : Ty} (ha : a.isData = true) (hb : b.isData = true) (h : (Ty.tuple [a, b]).isData = true)
    {x : a.den0} {y : b.den0} {cx : Code a} {cy : Code b} (hx : Smt.Rel M L a (Ty.up a ha x) cx)
    (hy : Smt.Rel M L b (Ty.up b hb y) cy) : Smt.Rels M L [a, b] (Ty.up (.tuple [a, b]) h (x, y, ())) (cx, cy, ()) := by
  show Smt.Rel M L _ (Ty.up (.tuple [a, b]) h (x, y, ())).1 cx ∧
    Smt.Rels M L [b] (Ty.up (.tuple [a, b]) h (x, y, ())).2 (cy, ())
  erw [Ty.up_tuple _ _ _ ha (by simp [Ty.isData, Ty.isDatas, hb])]
  refine ⟨hx, ?_⟩
  show Smt.Rel M L _ (Ty.up (.tuple [b]) (by simp [Ty.isData, Ty.isDatas, hb]) (y, ())).1 cy ∧ True
  erw [Ty.up_tuple _ _ _ hb rfl]; exact ⟨hy, trivial⟩

end

section
variable {M : Model} {L : Layout}

/-- `accepts`' condition in a request's admission is exact. -/
theorem admit_exact {r i c : Ty} (hi : i.isData = true) (accepts : Fun (Ty.fn [i] Ty.rules))
    {ac : Code (Ty.fn [i] Ty.rules)} {ca : Term} (hcode : accepts.code L = .ok (ac, ca)) (hca : Holds M ca)
    {ks : List Term} (input : i.den0) {records now fresh sc si : Term} (hsi : RelV L i (Ty.up _ hi input) (si.denote M))
    {a : AdmitOut r i c} {c1 : Term} (henc : encodeAdmit L ac ks records now fresh sc si = .ok (a, c1)) :
    Holds M c1 ↔ accepts.appFits L.count (input, ()) := by
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨ic, h3, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨rs, c1'⟩, h4, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  have hic : Smt.Rel M L _ (Ty.up _ hi input) ic := (rel_ofTerm (need_ok.1 h3) _).2 hsi
  exact accepts.app_exact hcode hca (by simp only [List.mem_singleton, forall_eq]; exact ofTerm_notFn (need_ok.1 h3))
    _ _ (rels1 hi accepts.args_data hic) h4

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

section
variable {M : Model} {L : Layout}

theorem holds_ite_hit {c a : Term} : Holds M (.ite c a tt) ↔ (Holds M c → Holds M a) := by
  rw [holds_ite]; unfold Holds; cases (c.denote M).toBool <;> simp; rfl

theorem tupleCodes_notFn {d : Nat} {x : Term} : (Γ : List Ty) → (i : Nat) → (σ : Codes Γ) →
    tupleCodes d Γ x i = some σ → ∀ t ∈ Γ, t.isFn = false
  | [], _, _, _ => by simp
  | t :: Γ, i, (c, cs), h => by
    cases hc : Code.ofTerm? t (Term.sel d 0 i x) with
    | none => simp [tupleCodes, hc] at h
    | some c' =>
    cases hcs : tupleCodes d Γ x (i + 1) with
    | none => simp [tupleCodes, hc, hcs] at h
    | some cs' =>
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ofTerm_notFn hc
    · exact tupleCodes_notFn Γ (i + 1) cs' hcs u hu

end

section
variable {v : ServiceV}

/-- Whether a query's `ensures`, if any, fits as a source and at the input and the answer. -/
def ensuresFits (S : Ty → Nat) {i a : Ty} : Option (Fun (Ty.fn [i, a] Ty.rules)) → i.den0 → a.den0 → Prop
  | none, _, _ => True
  | some f, x, y => (f.fits S).1 ∧ f.appFits S (x, y, ())

end

end Tazuna.Smt
