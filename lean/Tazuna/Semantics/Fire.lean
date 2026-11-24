import Tazuna.Semantics.Step

/-! What one round of `fire` does, in the form a table encoding reads. The step visits machines in order and each
machine's instances in key order, and the first instance whose deadline is the earliest due one fires (`fireFirst`,
`fireMachines`, `fire_succ`). Instances are kept in key order with no key twice, so within a machine the instance that
fires is the one with that deadline and the least key (`fireFirst_eq`): a condition on each instance and the set of
all of them, which a table, whose slots have no order, can state slot by slot. -/

namespace Tazuna.Ir

namespace Step

variable {r e : Ty}

/-- Whether an instance's timer has the deadline `d`. -/
def hitsAt {m : MachineV r e} (d : Int) (i : Instance m) : Bool :=
  match i.timer with
  | some (d', _) => decide (d' = d)
  | none => false

/-- An instance whose timer fires: it enters the state its timer names. -/
def fired (m : MachineV r e) (records : r.den0) (now : Int) (i : Instance m) : Instance m × List (Sender × EffectV e) :=
  match i.timer with
  | some (_, target) => enter m records now i.key target
  | none => (i, [])

theorem fired_key (m : MachineV r e) (records : r.den0) (now : Int) (i : Instance m) :
    (fired m records now i).1.key = i.key := by
  unfold fired; split <;> rfl

/-- The first instance whose timer has the deadline `d` fires; the flag says whether one did. -/
def fireFirst (m : MachineV r e) (records : r.den0) (now : Int) (d : Int) :
    List (Instance m) → List (Instance m) × List (Sender × EffectV e) × Bool
  | [] => ([], [], false)
  | i :: is =>
    if hitsAt d i then ((fired m records now i).1 :: is, (fired m records now i).2, true)
    else let x := fireFirst m records now d is; (i :: x.1, x.2.1, x.2.2)

/-- One round over the machines in order: unless an earlier one fired (`done`), a machine's first instance with the
deadline `d` fires. -/
def fireMachines (records : r.den0) (now : Int) (d : Int) :
    Bool → List (MachineState r e) → List (MachineState r e) × List (Sender × EffectV e) × Bool
  | done, [] => ([], [], done)
  | true, ms :: rest => let x := fireMachines records now d true rest; (ms :: x.1, x.2.1, true)
  | false, ⟨m, insts⟩ :: rest =>
    let y := fireFirst m records now d insts
    let x := fireMachines records now d y.2.2 rest
    (⟨m, y.1⟩ :: x.1, y.2.1 ++ x.2.1, x.2.2)

/-- The deadlines of the timers due at `now`. -/
def dues (machines : List (MachineState r e)) (now : Int) : List Int :=
  machines.flatMap fun ⟨_, insts⟩ => insts.filterMap fun i => i.timer.bind fun (d, _) => if d ≤ now then some d else none

theorem fireMachines_true (records : r.den0) (now d : Int) :
    (l : List (MachineState r e)) → fireMachines records now d true l = (l, [], true)
  | [] => rfl
  | ms :: l => by simp [fireMachines, fireMachines_true records now d l]

theorem fireFirst_fold {m : MachineV r e} {records : r.den0} {now d : Int}
    (G : List (Instance m) × List (Sender × EffectV e) × Bool → Instance m →
      List (Instance m) × List (Sender × EffectV e) × Bool)
    (h1 : ∀ acc effs i, G (acc, effs, true) i = (acc ++ [i], effs, true))
    (h2 : ∀ acc effs i, G (acc, effs, false) i = if hitsAt d i then
      (acc ++ [(fired m records now i).1], effs ++ (fired m records now i).2, true) else (acc ++ [i], effs, false)) :
    (insts : List (Instance m)) → (acc : List (Instance m)) → (effs : List (Sender × EffectV e)) → (done : Bool) →
      insts.foldl G (acc, effs, done) = if done then (acc ++ insts, effs, true) else
        (acc ++ (fireFirst m records now d insts).1, effs ++ (fireFirst m records now d insts).2.1,
          (fireFirst m records now d insts).2.2)
  | [], acc, effs, done => by cases done <;> simp [fireFirst]
  | i :: is, acc, effs, true => by
    rw [List.foldl_cons, h1, fireFirst_fold G h1 h2 is]; simp
  | i :: is, acc, effs, false => by
    rw [List.foldl_cons, h2]
    unfold fireFirst
    split
    · rw [fireFirst_fold G h1 h2 is]; simp
    · rw [fireFirst_fold G h1 h2 is]; simp

/-- A round of `fire`: no timer due ends it, else the instance `fireMachines` picks at the earliest due deadline
enters its timer's state and the rounds go on. -/
theorem fire_succ {v : ServiceV} (s : State v) (fuel : Nat) :
    fire s (fuel + 1) = match (dues s.machines s.now).min? with
      | none => some (s, [])
      | some d =>
        let x := fireMachines s.records s.now d false s.machines
        (fire { s with machines := x.1 } fuel).map fun (s', es) => (s', x.2.1 ++ es) := by
  rw [fire]
  show (match (dues s.machines s.now).min? with | none => _ | some d => _) = _
  split
  · rfl
  · rename_i d _
    have outer : ∀ (F : List (MachineState v.records v.event) × List (Sender × EffectV v.event) × Bool →
        MachineState v.records v.event → List (MachineState v.records v.event) × List (Sender × EffectV v.event) × Bool),
        (∀ acc effs ms, F (acc, effs, true) ms = (acc ++ [ms], effs, true)) →
        (∀ acc effs m insts, F (acc, effs, false) ⟨m, insts⟩ = (acc ++ [⟨m, (fireFirst m s.records s.now d insts).1⟩],
          effs ++ (fireFirst m s.records s.now d insts).2.1, (fireFirst m s.records s.now d insts).2.2)) →
        ∀ (l : List (MachineState v.records v.event)) acc effs done, l.foldl F (acc, effs, done) =
          (acc ++ (fireMachines s.records s.now d done l).1, effs ++ (fireMachines s.records s.now d done l).2.1,
            (fireMachines s.records s.now d done l).2.2) := by
      intro F g1 g2 l
      induction l with
      | nil => intro acc effs done; simp [fireMachines]
      | cons ms l ih =>
        intro acc effs done
        cases done with
        | true => rw [List.foldl_cons, g1, ih]; simp [fireMachines, fireMachines_true]
        | false => obtain ⟨m, insts⟩ := ms; rw [List.foldl_cons, g2, ih]; simp [fireMachines]
    have inner : ∀ (m : MachineV v.records v.event) (G : List (Instance m) × List (Sender × EffectV v.event) × Bool →
        Instance m → List (Instance m) × List (Sender × EffectV v.event) × Bool),
        (∀ acc effs i, G (acc, effs, true) i = (acc ++ [i], effs, true)) →
        (∀ acc effs i, G (acc, effs, false) i = match i.timer with
          | some (d', target) => if d' = d then
              let x := enter m s.records s.now i.key target; (acc ++ [x.1], effs ++ x.2, true)
            else (acc ++ [i], effs, false)
          | none => (acc ++ [i], effs, false)) →
        ∀ (insts : List (Instance m)) acc effs (done : Bool), insts.foldl G (acc, effs, done) = if done then (acc ++ insts, effs, true) else
          (acc ++ (fireFirst m s.records s.now d insts).1, effs ++ (fireFirst m s.records s.now d insts).2.1,
            (fireFirst m s.records s.now d insts).2.2) := by
      intro m G g1 g2
      refine fireFirst_fold G g1 fun acc effs i => ?_
      rw [g2]
      obtain ⟨k, st, t⟩ := i
      cases t with
      | none => rfl
      | some p =>
        obtain ⟨d', tg⟩ := p
        by_cases h : d' = d <;> simp [h, hitsAt, fired]
    rw [outer]
    · simp
    · intro acc effs ms
      obtain ⟨m, insts⟩ := ms
      simp only
      rw [inner m]
      · simp
      all_goals
        intro acc effs i
        obtain ⟨k, st, t⟩ := i
        cases t with
        | none => rfl
        | some p => obtain ⟨d', tg⟩ := p; rfl
    · intro acc effs m insts
      simp only
      rw [inner m]
      · simp
      all_goals
        intro acc effs i
        obtain ⟨k, st, t⟩ := i
        cases t with
        | none => rfl
        | some p => obtain ⟨d', tg⟩ := p; rfl

section
variable (T : List TypeDecl)

/-- Whether `i` fires among `insts` at the deadline `d`: its deadline is `d` and no instance with that deadline has a
smaller key. -/
def firesIn (m : MachineV r e) (d : Int) (insts : List (Instance m)) (i : Instance m) : Bool :=
  hitsAt d i && insts.all fun j => !hitsAt d j || (Ty.cmp T m.key i.key j.key).isLE

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
      (insts.map fun i => if firesIn T m d insts i then (fired m records now i).1 else i,
        (insts.filter (firesIn T m d insts)).flatMap fun i => (fired m records now i).2,
        insts.any (hitsAt d))
  | [], _, _ => rfl
  | i :: is, hs, hu => by
    rw [List.pairwise_cons] at hs hu
    unfold fireFirst
    split
    · rename_i hi
      have hfi : firesIn T m d (i :: is) i = true := by
        simp only [firesIn, hi, Bool.true_and, List.all_cons, cmp_isLE_refl, Bool.or_true, List.all_eq_true]
        exact fun j hj => by simp [hs.1 j hj]
      have hfj : ∀ j ∈ is, firesIn T m d (i :: is) j = false := by
        intro j hj
        simp only [firesIn, List.all_cons, hi, Bool.not_true, Bool.false_or, Bool.and_eq_false_iff]
        refine Or.inr (Or.inl ?_)
        cases h : (Ty.cmp T m.key j.key i.key).isLE
        · rfl
        · have := cmp_antisymm T ho (hs.1 j hj) h
          rw [hu.1 j hj] at this; cases this
      have hmap : is.map (fun j => if firesIn T m d (i :: is) j then (fired m records now j).1 else j) = is := by
        conv => rhs; rw [← List.map_id is]
        exact List.map_congr_left fun j hj => by simp [hfj j hj]
      have hfil : is.filter (firesIn T m d (i :: is)) = [] := List.filter_eq_nil_iff.2 fun j hj => by simp [hfj j hj]
      simp [hfi, hmap, hfil, hi]
    · rename_i hi
      have hi' : hitsAt d i = false := by simpa using hi
      have hfi : firesIn T m d (i :: is) i = false := by simp [firesIn, hi']
      have hsame : ∀ j, firesIn T m d (i :: is) j = firesIn T m d is j := by
        intro j; simp [firesIn, hi']
      rw [fireFirst_eq m ho records now d is hs.2 hu.2]
      simp only [List.map_cons, hfi, List.filter_cons, List.any_cons, hi', Bool.false_or, hsame]
      have hfi' : firesIn T m d is i = false := (hsame i) ▸ hfi
      simp only [hfi', Bool.false_eq_true, ite_false, Prod.mk.injEq, true_and]
      rw [List.filter_congr fun j _ => hsame j]
      simp

end

end Step

end Tazuna.Ir
