import Tazuna.Smt.Checked
import Tazuna.Semantics.Valid

/-! T5 for a checked spec (`diamond_confluent`): where every two waiting own effects commute in the canonical sense
(`Step.PairCommutes`) and timers fire forward (`Step.FiresForward`), the order the semantics picks for a cascade and
for a clock line's timers is not a choice the spec makes: every other order ends the same, up to renaming, or faults
as well. It needs no hypothesis about the program: every service of a spec that passed check respects every renaming
of the ids steps make (`CheckedSpec.equivariant`), since the spec is what a closed program evaluates to and evaluation
relates a closed program's value to itself under every renaming (`Expr.eval_rel`), which for structure values says
that the functions and values they keep relate to themselves. -/

namespace Tazuna.Smt

open Tazuna.Ir

mutual
theorem comparable_of_plain : (t : Ty) → t.plain = true → t.comparable = true
  | .int, _ | .date, _ | .str, _ | .id, _ => rfl
  | .tuple ts, h => comparables_of_plains ts h
  | .adt _ _ vs, h => comparabless_of_plainss vs h
  | .list _, h | .bag _, h | .table .., h | .fn .., h | .param _, h | .dsl .., h => by simp [Ty.plain] at h
theorem comparables_of_plains : (ts : List Ty) → Ty.plains ts = true → Ty.comparables ts = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Ty.plains, Bool.and_eq_true] at h
    simp [Ty.comparables, comparable_of_plain t h.1, comparables_of_plains ts h.2]
theorem comparabless_of_plainss : (vs : List (List Ty)) → Ty.plainss vs = true → Ty.comparabless vs = true
  | [], _ => rfl
  | ts :: vs, h => by
    simp only [Ty.plainss, Bool.and_eq_true] at h
    simp [Ty.comparabless, comparables_of_plains ts h.1, comparabless_of_plainss vs h.2]
end

mutual
theorem comparable_of_embeddable : (t : Ty) → t.embeddable = true → t.comparable = true
  | .int, _ | .date, _ | .str, _ | .id, _ => rfl
  | .dsl k _, h => h
  | .adt 0 _ vs, h => by
    simp only [Ty.embeddable, Option.isSome_iff_exists] at h
    obtain ⟨⟨rfl⟩, _⟩ := h
    rfl
  | .adt (_ + 1) _ vs, h => comparabless_of_embeddabless vs h
  | .tuple ts, h => comparables_of_embeddables ts h
  | .list t, h | .bag t, h => comparable_of_embeddable t h
  | .table k v, h => by
    simp only [Ty.embeddable, Bool.and_eq_true] at h
    simp [Ty.comparable, comparable_of_embeddable k h.1, comparable_of_embeddable v h.2]
  | .fn _ _, h | .param _, h => by simp [Ty.embeddable] at h
theorem comparables_of_embeddables : (ts : List Ty) → Ty.embeddables ts = true → Ty.comparables ts = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Ty.embeddables, Bool.and_eq_true] at h
    simp [Ty.comparables, comparable_of_embeddable t h.1, comparables_of_embeddables ts h.2]
theorem comparabless_of_embeddabless : (vs : List (List Ty)) → Ty.embeddabless vs = true → Ty.comparabless vs = true
  | [], _ => rfl
  | ts :: vs, h => by
    simp only [Ty.embeddabless, Bool.and_eq_true] at h
    simp [Ty.comparabless, comparables_of_embeddables ts h.1, comparabless_of_embeddabless vs h.2]
end

/-- Every service of a checked spec respects every renaming of the ids steps make: its functions and the values they
captured relate to themselves under every renaming, and its caller and key types are comparable. -/
theorem CheckedSpec.equivariant (c : CheckedSpec) : ∀ v ∈ c.spec.services, v.Equivariant := by
  intro v hv
  have hk := c.checked v hv
  refine ⟨?_, fun m hm => comparable_of_plain _ (Ty.plain_of_orderable _ (hk.keys m hm).1), fun R => ?_⟩
  · have h := hk.stateTys
    simp only [ServiceV.stateTys, Bool.and_eq_true] at h
    exact comparable_of_embeddable _ h.2.1
  · exact Var.get_rel c.program.root (Defs.eval_rel (R := R) c.program.defs) () () trivial rfl v hv

/-- A checked spec's machines keep states of comparable types: their instance tables are embeddable. -/
theorem CheckedSpec.states (c : CheckedSpec) {v : ServiceV} (hv : v ∈ c.spec.services) :
    ∀ m ∈ v.machines, m.state.comparable = true := fun m hm => by
  have h := (c.checked v hv).stateTys
  simp only [ServiceV.stateTys, Bool.and_eq_true, List.all_eq_true] at h
  have hm' := (h.1.1.1.2 m hm)
  simp only [MachineV.table, instEntry, Ty.embeddable, Ty.embeddables, Bool.and_eq_true] at hm'
  exact comparable_of_embeddable _ hm'.1.2.1

/-- T5: in a checked spec's service, where every two own effects waiting in a step in progress whose names are below
its counter commute in the canonical sense, every order of a cascade ends as `settle` does, up to renaming the ids the
cascade made (names from before it stay as they are) and reading collections as multisets, or both fault; and where its timers fire forward, every order of the timers due at
one deadline of a clock line ends as `fire` does, with the same state and the same effects in some order. -/
theorem diamond_confluent (c : CheckedSpec) {v : ServiceV} (hv : v ∈ c.spec.services)
    (hpairs : ∀ a : Step.Acc v, Step.Supp a → ∀ i j (hi : i < a.own.length) (hj : j < a.own.length), i ≠ j →
      Step.PairCommutes c.T { a with own := Step.dropTwo a.own i j } a.own[i] a.own[j])
    (htimers : Step.FiresForward v.machines) :
    (∀ fuel (a : Step.Acc v), Step.Supp a → ∀ {r}, Diamond.Runs (Step.ownSys c.T v) fuel a r →
      Diamond.Agree (Step.Same a.state.fresh a.state.nextId) r (Step.settle c.T fuel a)) ∧
    (∀ fuel (s : State v) {r}, Diamond.Runs (Step.timerSys v) fuel (s, []) r →
      Diamond.Agree Step.TimerEq r (Step.fireResult s (fuel + 1))) :=
  ⟨fun fuel a ha _ hr => Step.cascade_agrees c.T (c.equivariant v hv) (J := fun _ => True) (fun _ _ _ _ _ _ => trivial)
      (fun a ha _ => hpairs a ha) fuel a ha trivial hr,
    fun fuel s _ hr => Step.timers_agree htimers fuel s hr⟩

/-- T5 for runs: the cascades `diamond_confluent` speaks about are every cascade a run starts. From the initial state
on valid inputs (each carries only ids the service made before or names from outside, which traces and scenarios
guarantee by how they name ids), every state keeps its names below its counter, so every cascade a step starts
(`Step.Begins`) ends, in every order, as `settle` does, up to renaming, or faults in both. -/
theorem runs_confluent (c : CheckedSpec) {v : ServiceV} (hv : v ∈ c.spec.services)
    (hpairs : ∀ a : Step.Acc v, Step.Supp a → ∀ i j (hi : i < a.own.length) (hj : j < a.own.length), i ≠ j →
      Step.PairCommutes c.T { a with own := Step.dropTwo a.own i j } a.own[i] a.own[j])
    (htimers : Step.FiresForward v.machines) {xs : List (Input v)} (hxs : Step.ValidRun c.T (Step.State.init v) xs)
    {x : Input v} (hx : x.Valid (run c.T v (Step.State.init v) xs).1) {a : Step.Acc v}
    (ha : Step.Begins c.T (run c.T v (Step.State.init v) xs).1 x a) :
    ∀ fuel {r}, Diamond.Runs (Step.ownSys c.T v) fuel a r →
      Diamond.Agree (Step.Same a.state.fresh a.state.nextId) r (Step.settle c.T fuel a) := by
  have he := c.equivariant v hv
  have hr := (c.checked v hv).reach
  have hi := run_inv c.T hr _ Step.init_inv xs
  have hs := Step.run_supp c.T he (c.states hv) hr _ Step.init_inv (Step.init_supp he) xs hxs
  have hsa := (Step.begins_supp c.T he (c.states hv) hs hi.below hx ha).1
  exact fun fuel _ hrun => (diamond_confluent c hv hpairs htimers).1 fuel a hsa hrun

end Tazuna.Smt
