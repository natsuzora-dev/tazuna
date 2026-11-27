import Tazuna.Smt.PairLine

/-! Every own effect waiting in a cascade is coded by a value of the effect datatype (`QueueCoded`), wherever the
cascade starts with such effects and every step it takes fits the slots: an own step's encoding relates each own
effect it queues to a value of the effect datatype (`AccRel`'s own slots). Where the pair lines read `Prove.proved`, every step from a state that fits the
slots fits too (the bound question of the effect's pair with itself is unsat), so the lines need no more than the
states to fit; where they read `Prove.withinBounds`, the steps' fit is the scope they state. -/

namespace Tazuna.Smt

open Tazuna.Ir

section
variable {L : Layout} {M : Model} {T : List TypeDecl} {v : ServiceV}

/-- A pair question's encoding of its first step: where the codes hold and the effect's own step fits the slots, each
own effect the step queues is coded. -/
theorem pair_queued {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v)
    (senv : StepEnv L (shapes v)) {S : SymState v} {a0 : Step.Acc v} (hR : StateRel M L T (shapes v) S a0.state)
    {t1 t2 : Term} {x1 : OwnEffectV v.event}
    (hx1 : RelV L (.dsl .effect [v.event]) x1.effect (t1.denote M))
    (hreach1 : x1.effect.Reach P)
    {k1 k2 : OwnPlace L v.event} (ht1 : Holds M (.is senv.dE (L.ownCtor v.event k1) t1))
    {o : PairOut} (henc : encodePair L T P v senv S t1 t2 k1 k2 = .ok o) (hcodes : Holds M o.codes)
    (hfit : ownFits L.count T a0.state x1) :
    ∀ b, Step.runOwn T a0 x1 = .ok b → ∃ os, b.own = a0.own ++ os ∧ ∀ y ∈ os, ∃ z, RelV L (.dsl .effect [v.event]) y.effect z := by
  obtain ⟨⟨apply, ca⟩, happ, henc⟩ := bind_ok.1 henc
  obtain ⟨⟨⟨ko1, a1⟩, c1, y1⟩, h1, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  obtain ⟨_, -, henc⟩ := bind_ok.1 henc
  cases pure_ok.1 henc
  simp only [holds_allT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hcodes
  obtain ⟨hca, hy1, -, -, -⟩ := hcodes
  have hshs : ∀ sh ∈ shapes v, sh.InSites P := fun _ => shapes_inSites chk.reach
  obtain ⟨vals1, he1, hk1⟩ := own_key hx1 ht1 rfl
  have hq0 : (Term.int 0).denote M = .int ((0 : Nat) : Int) := rfl
  have eA1 := ownKind_encode chk hshs (shapesHold_shapes v) a0 happ hca senv hR.records hR.now hR.fresh hR.nextId hq0
    hR.machines x1 hreach1 he1 hk1 h1 hy1
  obtain ⟨-, hA1⟩ := eA1.2 (eA1.1.2 hfit)
  intro b hb
  revert hA1
  cases ko1.fault? M with
  | some g => intro hA1; rw [hA1] at hb; cases hb
  | none =>
    intro hA1
    rw [hb] at hA1
    obtain ⟨-, -, -, -, -, os, hos, -, hrel⟩ := hA1.ends
    exact ⟨os, hos, ownRel_coded hrel⟩

end

section
variable {L : Layout} {T : List TypeDecl} {v : ServiceV}

/-- What the pair lines say of a waiting own effect's step from a state that fits the slots: where each line reads
proved, or within the bounds and the step fits, each own effect the step queues is coded. -/
theorem queued_at {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (hL : SortedLayout L)
    (senv : StepEnv L (shapes v))
    {a0 : Step.Acc v} (hkeys : Step.KeysOk T a0.state) (hW : Within L (shapes v) a0.state)
    (hinv : Step.Inv P a0.state) (hsupp : Step.StateSupp a0.state) (hqk : Step.QueueOk P a0)
    {x : OwnEffectV v.event} (hx : ∃ z, RelV L (.dsl .effect [v.event]) x.effect z)
    (hreach : x.effect.Reach P)
    (hcf : ∀ p ∈ L.ownPairs v.event, PairLine L T P v senv (ownFits L.count T a0.state x) p) :
    ∀ b, Step.runOwn T a0 x = .ok b → ∃ os, b.own = a0.own ++ os ∧ ∀ y ∈ os, ∃ z, RelV L (.dsl .effect [v.event]) y.effect z := by
  obtain ⟨M, hM, hsel, hS, hx1, hx2⟩ := pair_model hkeys hW hx hx
  obtain ⟨p, hp, ht1, ht2⟩ := pair_kinds senv hx1 hx2
  obtain ⟨bq, tq, hq, -, hor⟩ := hcf p hp
  obtain ⟨o, ho, hb, -⟩ := pair_unfold chk hL senv hq hM hsel hS hinv.below hsupp hx1 hx2 ht1 ht2 hreach hreach
  have hR := decode_state hS
  have hfit : Holds M o.codes ∧ ownFits L.count T a0.state x := hor.elim
    (fun h => ⟨(hb h).1, ((pair_fits chk senv hR hinv hqk hx1 hx2 hreach hreach ht1 ht2 ho (hb h).1).1
      (hb h).2).1⟩)
    fun ⟨hpc, hof⟩ => ⟨(pair_codes ho).2 hpc, hof⟩
  exact pair_queued chk senv hR (t1 := .var (pairVar v)) hx1 hreach ht1 ho hfit.1 hfit.2

/-- A cascade's step keeps every waiting own effect coded where the pair lines speak for it (`queued_at`). -/
theorem coded_step {P : List AnySite} {E : List AnyEffectSite} (chk : Checked P E T v) (hL : SortedLayout L)
    (senv : StepEnv L (shapes v))
    {a : Step.Acc v} (hkeys : Step.KeysOk T a.state) (hW : Within L (shapes v) a.state) (hinv : Step.Inv P a.state)
    (hsupp : Step.Supp a) (hqk : Step.QueueOk P a)
    (hc : QueueCoded L a) {i : Nat} (hi : i < a.own.length)
    (hcf : ∀ p ∈ L.ownPairs v.event, PairLine L T P v senv (ownFits L.count T a.state a.own[i]) p)
    {d : Step.Acc v} (hd : Step.runOwn T { a with own := a.own.eraseIdx i } a.own[i] = .ok d) : QueueCoded L d := by
  have hmem : a.own[i] ∈ a.own := List.getElem_mem hi
  have hq' : Step.QueueOk P { a with own := a.own.eraseIdx i } := fun x hx => hqk x (List.mem_of_mem_eraseIdx hx)
  have hs : Step.StateSupp a.state := fun P hP => (hsupp P hP).state
  obtain ⟨os, hos, hcod⟩ := queued_at chk hL senv (a0 := { a with own := a.own.eraseIdx i }) hkeys hW hinv hs hq'
    (hc _ hmem) (hqk _ hmem) hcf d hd
  intro y hy
  rw [hos] at hy
  rcases List.mem_append.1 hy with h | h
  · exact hc y (List.mem_of_mem_eraseIdx h)
  · exact hcod y h

end

end Tazuna.Smt
