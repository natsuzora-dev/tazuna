import Tazuna.Semantics.Step

/-! What one round of `fire` does, in the form a table encoding reads. The round visits machines in order and each
machine's instances in key order, and the first instance whose deadline is the earliest due one fires (`fireFirst`,
`fireMachines`). Instances are kept in key order with no key twice, so within a machine the instance that fires is the
one with that deadline and the least key (`fireFirst_eq`): a condition on each instance and the set of all of them,
which a table, whose slots have no order, can state slot by slot. -/

namespace Tazuna.Ir

namespace Step

variable {r e : Ty}

theorem fired_key (m : MachineV r e) (records : r.den0) (now : Int) (i : Instance m) :
    (fired m records now i).1.key = i.key := by
  unfold fired; split <;> rfl

theorem fireMachines_true (records : r.den0) (now d : Int) :
    {ms : List (MachineV r e)} → (l : Machines ms) → fireMachines records now d true l = (l, [], true)
  | _, .nil => rfl
  | _, .cons _ l => by simp [fireMachines, fireMachines_true records now d l]

theorem fireFirst_keys (m : MachineV r e) (records : r.den0) (now d : Int) :
    (insts : List (Instance m)) → (fireFirst m records now d insts).1.map (·.key) = insts.map (·.key)
  | [] => rfl
  | i :: is => by
    unfold fireFirst
    split
    · simp [fired_key]
    · simp [fireFirst_keys m records now d is]

/-- A round changes a machine's instances only by `fireFirst`. -/
theorem mem_fireMachines (records : r.den0) (now d : Int) : (b : Bool) → {ms : List (MachineV r e)} →
    (sms : Machines ms) → ∀ sm' ∈ (fireMachines records now d b sms).1.toSigma,
    ∃ sm ∈ sms.toSigma, sm' = sm ∨ sm' = ⟨sm.1, (fireFirst sm.1 records now d sm.2).1⟩
  | b, _, .nil, _, h => by cases b <;> simp [fireMachines] at h
  | true, _, .cons _ _, sm', h => by
    rw [fireMachines_true] at h
    exact ⟨sm', h, .inl rfl⟩
  | false, _, .cons insts rest, sm', h => by
    simp only [fireMachines, PerMachine.toSigma_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨⟨_, insts⟩, List.mem_cons_self, .inr rfl⟩
    · obtain ⟨sm, hsm, he⟩ := mem_fireMachines records now d _ rest sm' h
      exact ⟨sm, List.mem_cons_of_mem _ hsm, he⟩

theorem mem_fireFirst_effs (m : MachineV r e) (records : r.den0) (now d : Int) : (insts : List (Instance m)) →
    ∀ x ∈ (fireFirst m records now d insts).2.1, ∃ k st, x ∈ (enter m records now k st).2
  | [], _, h => nomatch h
  | i :: is, x, h => by
    unfold fireFirst at h
    split at h
    · unfold fired at h
      split at h
      · exact ⟨_, _, h⟩
      · nomatch h
    · exact mem_fireFirst_effs m records now d is x h

/-- Every effect a round starts is one an instance's entering a state starts. -/
theorem mem_fireMachines_effs (records : r.den0) (now d : Int) : (b : Bool) → {ms : List (MachineV r e)} →
    (sms : Machines ms) → ∀ x ∈ (fireMachines records now d b sms).2.1,
    ∃ sm ∈ sms.toSigma, ∃ k st, x ∈ (enter sm.1 records now k st).2
  | b, _, .nil, _, h => by cases b <;> simp [fireMachines] at h
  | true, _, .cons _ _, x, h => by rw [fireMachines_true] at h; nomatch h
  | false, _, .cons insts rest, x, h => by
    simp only [fireMachines, List.mem_append] at h
    rcases h with h | h
    · exact ⟨⟨_, insts⟩, List.mem_cons_self, mem_fireFirst_effs _ records now d insts x h⟩
    · obtain ⟨sm, hsm, he⟩ := mem_fireMachines_effs records now d _ rest x h
      exact ⟨sm, List.mem_cons_of_mem _ hsm, he⟩

section
variable (T : List TypeDecl)

/-- Whether `i` fires among `insts` at the deadline `d`: its deadline is `d` and no instance with that deadline has a
smaller key. -/
def firesIn (m : MachineV r e) (records : r.den0) (d : Int) (insts : List (Instance m)) (i : Instance m) : Bool :=
  hitsAt records d i && insts.all fun j => !hitsAt records d j || (Ty.cmp T m.key i.key j.key).isLE

theorem cmp_isLE_refl (t : Ty) (x : t.den0) : (Ty.cmp T t x x).isLE = true := by
  have := Std.OrientedCmp.eq_swap (cmp := Ty.cmp T t) (a := x) (b := x)
  cases h : Ty.cmp T t x x <;> simp_all [Ordering.swap]

theorem cmp_antisymm {t : Ty} (ho : t.ordered T = true) {x y : t.den0} (h1 : (Ty.cmp T t x y).isLE = true)
    (h2 : (Ty.cmp T t y x).isLE = true) : (Ty.semWith Dsl.base t).2 x y = true := by
  refine (Ty.cmp_eq_iff T ho x y).1 ?_
  rw [Std.OrientedCmp.eq_swap (cmp := Ty.cmp T t) (a := y) (b := x)] at h2
  cases h : Ty.cmp T t x y <;> simp_all [Ordering.swap]

/-- On instances in key order with no key twice, the first with the deadline `d` is the one with the least key. -/
theorem fireFirst_eq (m : MachineV r e) (ho : m.key.ordered T = true) (records : r.den0) (now d : Int) :
    (insts : List (Instance m)) → insts.Pairwise (fun a b => (Ty.cmp T m.key a.key b.key).isLE) →
    insts.Pairwise (fun a b => (Ty.semWith Dsl.base m.key).2 a.key b.key = false) →
    fireFirst m records now d insts =
      (insts.map fun i => if firesIn T m records d insts i then (fired m records now i).1 else i,
        (insts.filter (firesIn T m records d insts)).flatMap fun i => (fired m records now i).2,
        insts.any (hitsAt records d))
  | [], _, _ => rfl
  | i :: is, hs, hu => by
    rw [List.pairwise_cons] at hs hu
    unfold fireFirst
    split
    · rename_i hi
      have hfi : firesIn T m records d (i :: is) i = true := by
        simp only [firesIn, hi, Bool.true_and, List.all_cons, cmp_isLE_refl, Bool.or_true, List.all_eq_true]
        exact fun j hj => by simp [hs.1 j hj]
      have hfj : ∀ j ∈ is, firesIn T m records d (i :: is) j = false := by
        intro j hj
        simp only [firesIn, List.all_cons, hi, Bool.not_true, Bool.false_or, Bool.and_eq_false_iff]
        refine Or.inr (Or.inl ?_)
        cases h : (Ty.cmp T m.key j.key i.key).isLE
        · rfl
        · have := cmp_antisymm T ho (hs.1 j hj) h
          rw [hu.1 j hj] at this; cases this
      have hmap : is.map (fun j => if firesIn T m records d (i :: is) j then (fired m records now j).1 else j) = is := by
        conv => rhs; rw [← List.map_id is]
        exact List.map_congr_left fun j hj => by simp [hfj j hj]
      have hfil : is.filter (firesIn T m records d (i :: is)) = [] := List.filter_eq_nil_iff.2 fun j hj => by simp [hfj j hj]
      simp [hfi, hmap, hfil, hi]
    · rename_i hi
      have hi' : hitsAt records d i = false := by simpa using hi
      have hfi : firesIn T m records d (i :: is) i = false := by simp [firesIn, hi']
      have hsame : ∀ j, firesIn T m records d (i :: is) j = firesIn T m records d is j := by
        intro j; simp [firesIn, hi']
      rw [fireFirst_eq m ho records now d is hs.2 hu.2]
      simp only [List.map_cons, hfi, List.filter_cons, List.any_cons, hi', Bool.false_or, hsame]
      have hfi' : firesIn T m records d is i = false := (hsame i) ▸ hfi
      simp only [hfi', Bool.false_eq_true, ite_false, Prod.mk.injEq, true_and]
      rw [List.filter_congr fun j _ => hsame j]
      simp

end

theorem fired_effs (m : MachineV r e) (records : r.den0) (now : Int) (i : Instance m) :
    (fired m records now i).2.length ≤ 1 := by
  unfold fired
  split
  · unfold enter; cases m.effectAt _ _ _ _ <;> simp
  · simp

theorem fireFirst_effs (m : MachineV r e) (records : r.den0) (now d : Int) :
    (insts : List (Instance m)) → (fireFirst m records now d insts).2.1.length ≤ 1 ∧
      ((fireFirst m records now d insts).2.2 = false → (fireFirst m records now d insts).2.1 = [])
  | [] => ⟨by simp [fireFirst], fun _ => rfl⟩
  | i :: is => by
    unfold fireFirst
    split
    · exact ⟨fired_effs m records now i, fun h => nomatch h⟩
    · exact fireFirst_effs m records now d is

/-- A round fires at most one instance, so it starts at most one effect. -/
theorem fireMachines_effs (records : r.den0) (now d : Int) :
    (b : Bool) → {ms : List (MachineV r e)} → (sms : Machines ms) → (fireMachines records now d b sms).2.1.length ≤ 1
  | b, _, .nil => by cases b <;> simp [fireMachines]
  | true, _, .cons _ _ => by rw [fireMachines_true]; simp
  | false, _, .cons insts rest => by
    obtain ⟨h1, h2⟩ := fireFirst_effs _ records now d insts
    simp only [fireMachines, List.length_append]
    cases hb : (fireFirst _ records now d insts).2.2 with
    | true => rw [fireMachines_true]; simpa using h1
    | false => rw [h2 hb]; simpa using fireMachines_effs records now d false rest

end Step

end Tazuna.Ir
