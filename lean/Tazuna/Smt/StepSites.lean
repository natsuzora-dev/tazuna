import Tazuna.Smt.Step

/-! The cascade's codes condition is exact (entry 63's rule for every side condition). A step's `sites` term is the
conjunction, over each place of the cascade, of the codes condition of every own kind's command or query, built at
the closure records the structure holds, so it does not depend on the state: it holds exactly when the cascade may
run (a positive `cascade` bound) only where every own command's and query's functions fit their slots
(`SitesFit`). `step_sites` proves it for every input kind, so a script that asserts `sites` loses no real step, and
one where it fails is a bound reached, never a false proof. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {v : ServiceV}

/-- Whether the functions of the command or query an own kind runs fit their slots; a kind that runs none asks
nothing. -/
def OwnShape.CodesFit (S : Ty → Nat) : OwnShape v → Prop
  | .command x _ _ => (x.accepts.fits S).1 ∧ (x.decide.fits S).1 ∧ (x.ensures.fits S).1
  | .query x _ _ => (x.accepts.fits S).1 ∧ (x.resolve.fits S).1
  | .unlisted _ | .unreached _ => True

/-- Whether every own kind of the layout runs functions that fit, wherever the cascade may run. -/
def SitesFit (L : Layout) (P : List AnySite) (v : ServiceV) : Prop :=
  v.bounds.cascadeNat ≠ 0 → ∀ key ∈ L.ownsOf v.event, (ownShape v P key).CodesFit L.count

end

theorem forall2_forall_iff {α β : Type} {R : α → β → Prop} {p : α → Prop} {q : β → Prop}
    (hpq : ∀ a b, R a b → (p a ↔ q b)) : {as : List α} → {bs : List β} → Forall2 R as bs →
    ((∀ a ∈ as, p a) ↔ ∀ b ∈ bs, q b)
  | [], [], _ => by simp
  | a :: as, b :: bs, ⟨h, hs⟩ => by
    simp only [List.mem_cons, forall_eq_or_imp]
    rw [hpq a b h, forall2_forall_iff hpq hs]

theorem forall_zipIdx_iff {α : Type} (p : α → Prop) (l : List α) : (∀ x ∈ l.zipIdx, p x.1) ↔ ∀ a ∈ l, p a := by
  refine ⟨fun h a ha => ?_, fun h x hx => h _ (List.fst_mem_of_mem_zipIdx hx)⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ha
  exact h (a, i) (List.mem_zipIdx_iff_getElem?.2 hi)

section
variable {M : Model} {L : Layout} {T : List TypeDecl} {v : ServiceV} {P : List AnySite}
  {shs : List (PendingShape v.event)} {senv : StepEnv L shs} {apply : Code (Ty.fn [v.records, v.event] v.records)}

theorem ownKind_codes {nR : Nat} {records now fresh n q eff : Term} {xs : PerMachine (fun _ => Term) v.machines}
    {j : Nat} {key : OwnKey} {k : Encoded (OwnKindStep v)}
    (h : encodeOwnKind L T P v shs senv nR apply records now fresh n q eff xs j key = .ok k) :
    Holds M k.codes ↔ (ownShape v P key).CodesFit L.count := by
  unfold encodeOwnKind at h
  generalize ownShape v P key = sh at h ⊢
  cases sh with
  | unlisted _ | unreached _ => cases pure_ok.1 h; exact iff_of_true holds_tt trivial
  | command x Γ site =>
    obtain ⟨⟨cc, cx⟩, hcc, h⟩ := bind_ok.1 h
    obtain ⟨_, -, h⟩ := bind_ok.1 h
    obtain ⟨_, -, h⟩ := bind_ok.1 h
    obtain ⟨_, -, h⟩ := bind_ok.1 h
    obtain ⟨_, -, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact commandCode_exact hcc
  | query x Γ site =>
    obtain ⟨⟨qc, cq⟩, hqc, h⟩ := bind_ok.1 h
    obtain ⟨_, -, h⟩ := bind_ok.1 h
    obtain ⟨_, -, h⟩ := bind_ok.1 h
    obtain ⟨_, -, h⟩ := bind_ok.1 h
    obtain ⟨_, -, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    exact queryCode_exact hqc

theorem ownStep_codes {records now fresh n q eff : Term} {xs : PerMachine (fun _ => Term) v.machines}
    {o : OwnStepOut v} {c cx : Term}
    (h : encodeOwnStep L T P v shs senv apply records now fresh n q eff xs = .ok ⟨o, c, cx⟩) :
    Holds M cx ↔ ∀ key ∈ L.ownsOf v.event, (ownShape v P key).CodesFit L.count := by
  unfold encodeOwnStep at h
  obtain ⟨ks, hks, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  rw [holds_allT, List.forall_mem_map,
    ← forall_zipIdx_iff (fun key => (ownShape v P key).CodesFit L.count) (L.ownsOf v.event)]
  refine (forall2_forall_iff (p := fun kj => (ownShape v P kj.1).CodesFit L.count)
    (q := fun y => Holds M y.2.codes) ?_ (mapM_ok _ _ _ hks)).symm
  intro kj y hy
  obtain ⟨r, hr, hy⟩ := bind_ok.1 hy
  cases pure_ok.1 hy
  exact (ownKind_codes hr).symm

/-- The cascade's codes condition holds exactly when, wherever an internal step may run, every own kind's functions
fit. -/
theorem settle_codes {dflt now : Term} :
    (fuel k : Nat) → (S : List OwnSlot) → (t : StepTerms v) → {o : SettleOut v} → {c cx : Term} →
    encodeSettle L T P v shs senv apply dflt now fuel k S t = .ok ⟨o, c, cx⟩ →
    (Holds M cx ↔ (fuel ≠ 0 → ∀ key ∈ L.ownsOf v.event, (ownShape v P key).CodesFit L.count))
  | 0, _, _, _, _, _, _, h => by
    simp only [encodeSettle] at h
    cases pure_ok.1 h
    exact iff_of_true holds_tt (fun h => absurd rfl h)
  | f + 1, k, S, t, _, _, _, h => by
    simp only [encodeSettle] at h
    obtain ⟨⟨o1, c1, cx1⟩, h1, h⟩ := bind_ok.1 h
    obtain ⟨⟨rest, c', cx'⟩, h2, h⟩ := bind_ok.1 h
    cases pure_ok.1 h
    rw [holds_andT, ownStep_codes h1, settle_codes f _ _ _ h2]
    exact ⟨fun ⟨a, _⟩ _ => a, fun a => ⟨a (by omega), fun _ => a (by omega)⟩⟩

theorem finish_codes {inv : Code (Ty.fn [v.records] Ty.rules)} {now fresh pending : Term} {eo : EventsOut v}
    {fo : FinishOut v} {c cx : Term} (h : encodeFinish L T P v shs senv apply inv now fresh pending eo = .ok ⟨fo, c, cx⟩) :
    Holds M cx ↔ SitesFit L P v := by
  unfold encodeFinish at h
  obtain ⟨⟨so, cs, cx'⟩, h1, h⟩ := bind_ok.1 h
  obtain ⟨_, -, h⟩ := bind_ok.1 h
  obtain ⟨_, -, h⟩ := bind_ok.1 h
  obtain ⟨_, -, h⟩ := bind_ok.1 h
  cases pure_ok.1 h
  exact settle_codes _ _ _ _ h1

end

section
variable {M : Model} {L : Layout} {T : List TypeDecl}

/-- Exactness of the sites condition for every step kind: a step whose kind ends with a cascade has it exactly when
every own kind's functions fit wherever the cascade may run; a query and an unmatched answer ask nothing. -/
theorem step_sites {P : List AnySite} {v : ServiceV} (senv : StepEnv L (shapes v)) (S : SymState v)
    {inp : SymInput v (shapes v) senv.nT} {t : EncodedStep v} (henc : encodeStep L T P v senv S inp = .ok t) :
    Holds M t.sites ↔ match inp with
      | .query .. | .unmatched .. => True
      | _ => SitesFit L P v := by
  cases inp with
  | command i sc si =>
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c, cs⟩, hcmd, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    unfold encodeCommand at hcmd
    obtain ⟨_, -, hcmd⟩ := bind_ok.1 hcmd
    obtain ⟨_, -, hcmd⟩ := bind_ok.1 hcmd
    obtain ⟨_, -, hcmd⟩ := bind_ok.1 hcmd
    obtain ⟨⟨fo, cf, cfx⟩, hf, hcmd⟩ := bind_ok.1 hcmd
    cases pure_ok.1 hcmd
    exact finish_codes hf
  | query i sc si =>
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    exact iff_of_true holds_tt trivial
  | answer k j toT valT =>
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c, cs⟩, hans, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    unfold encodeAnswer at hans
    iterate 9 obtain ⟨_, -, hans⟩ := bind_ok.1 hans
    obtain ⟨⟨fo, cf, cfx⟩, hf, hans⟩ := bind_ok.1 hans
    cases pure_ok.1 hans
    exact finish_codes hf
  | unmatched ty toT valT =>
    cases pure_ok.1 henc
    exact iff_of_true holds_tt trivial
  | event i sv =>
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c, cs⟩, hev, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    unfold encodeEvent at hev
    obtain ⟨_, -, hev⟩ := bind_ok.1 hev
    obtain ⟨_, -, hev⟩ := bind_ok.1 hev
    obtain ⟨⟨fo, cf, cfx⟩, hf, hev⟩ := bind_ok.1 hev
    cases pure_ok.1 hev
    exact finish_codes hf
  | clock st =>
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨_, -, henc⟩ := bind_ok.1 henc
    obtain ⟨⟨o, c, cs⟩, hcl, henc⟩ := bind_ok.1 henc
    cases pure_ok.1 henc
    unfold encodeClock at hcl
    obtain ⟨_, -, hcl⟩ := bind_ok.1 hcl
    obtain ⟨⟨fo, cf, cfx⟩, hf, hcl⟩ := bind_ok.1 hcl
    cases pure_ok.1 hcl
    exact finish_codes hf

end

end Tazuna.Smt
