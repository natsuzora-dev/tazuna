import Tazuna.Semantics.PendingInv

/-! The own queue read as an append-only list. `settle` pops the queue's head before each internal step, and an
internal step only appends to the queue (`runOwn_own`), so the internal step `k` runs the `k`-th own effect queued in
all, counting from the queue the step began with, and `settle` is `settleFrom` over places in a list that is never
popped (`settle_eq_from`). This is the form the encoding unrolls: it numbers own effects by place, as it numbers
requests by wire id. -/

namespace Tazuna.Ir

variable {v : ServiceV}

namespace Step

theorem foldlM_map_comm {ε α β : Type} (g : α → β → Except ε α) (h : α → α) (hg : ∀ a x, g (h a) x = (g a x).map h) :
    (xs : List β) → (a : α) → xs.foldlM g (h a) = (xs.foldlM g a).map h
  | [], _ => rfl
  | x :: xs, a => by
    simp only [List.foldlM_cons, hg, bind, Except.bind, Except.map]
    cases g a x with
    | error e => rfl
    | ok a' => exact foldlM_map_comm g h hg xs a'

theorem map_bind_comm {ε α β : Type} (x : Except ε α) (f : α → α) (g g' : α → Except ε β) (h : β → β)
    (hg : ∀ a, g (f a) = (g' a).map h) : (x.map f >>= g) = (x >>= g').map h := by
  cases x <;> simp [Except.map, bind, Except.bind, hg]

/-- A command's run with `f` applied to the step in progress it leaves. -/
def Ran.map {j : Ty} (f : Acc v → Acc v) : Ran v j → Ran v j
  | .invalid rs => .invalid rs
  | .rejected a k => .rejected (f a) k
  | .accepted a => .accepted (f a)

/-- The accumulator with `xs` in front of its own queue. -/
def Acc.ownFront (xs : List (EffectV v.event)) (a : Acc v) : Acc v := { a with own := xs ++ a.own }

theorem start_own (xs : List (EffectV v.event)) (effs : List (Sender × EffectV v.event)) (a : Acc v) :
    start (a.ownFront xs) effs = (start a effs).map (Acc.ownFront xs) := by
  refine foldlM_map_comm _ (Acc.ownFront xs) ?_ effs a
  rintro a ⟨snd, eff⟩
  cases eff with
  | request r =>
    dsimp only
    split
    · rfl
    · simp [Except.map, Acc.ownFront]
  | command => simp [Except.map, Acc.ownFront]
  | query => simp [Except.map, Acc.ownFront]

theorem applyEvents_own (T : List TypeDecl) (xs : List (EffectV v.event)) (events : List v.event.den0) (a : Acc v) :
    applyEvents T (a.ownFront xs) events = (applyEvents T a events).map (Acc.ownFront xs) := by
  unfold applyEvents
  refine foldlM_map_comm _ (Acc.ownFront xs) (fun a ev => ?_) events a
  exact start_own xs (react T a.state ev).2 { a with state := (react T a.state ev).1, events := a.events ++ [ev] }

theorem execCommand_own (T : List TypeDecl) (xs : List (EffectV v.event)) (a : Acc v)
    (x : CommandV v.records v.event v.caller) (caller : v.caller.den0) (input : x.input.den0) :
    execCommand T (a.ownFront xs) x caller input = (execCommand T a x caller input).map (Ran.map (Acc.ownFront xs)) := by
  unfold execCommand
  rw [show ctx (a.ownFront xs).state (a.ownFront xs).state.records caller input =
    ctx a.state a.state.records caller input from rfl]
  split
  · rfl
  · simp only
    split
    · rw [show ({ a.ownFront xs with state := { (a.ownFront xs).state with fresh := (a.ownFront xs).state.fresh + 1 } }
          : Acc v) = Acc.ownFront xs { a with state := { a.state with fresh := a.state.fresh + 1 } } from rfl]
      erw [applyEvents_own T xs]
      refine map_bind_comm _ _ _ _ _ fun a1 => ?_
      rw [show (Acc.ownFront xs a1).state.records = a1.state.records from rfl]
      split <;> rfl
    · rfl

theorem runCommand_own (T : List TypeDecl) (xs : List (EffectV v.event)) (a : Acc v)
    (x : CommandV v.records v.event v.caller) (caller : v.caller.den0) (input : x.input.den0)
    (onAnswer : Fun (Ty.fn [Ty.result Ty.nil x.rejection] (.list v.event))) :
    runCommand T (a.ownFront xs) x caller input onAnswer =
      (runCommand T a x caller input onAnswer).map (Acc.ownFront xs) := by
  unfold runCommand
  rw [execCommand_own]
  refine map_bind_comm _ _ _ _ _ fun r => ?_
  cases r with
  | invalid => rfl
  | accepted a1 => exact applyEvents_own T xs _ a1
  | rejected a1 j => exact applyEvents_own T xs _ a1

theorem runQuery_own (T : List TypeDecl) (xs : List (EffectV v.event)) (a : Acc v) (x : QueryV v.records v.caller)
    (caller : v.caller.den0) (input : x.input.den0) (onAnswer : Fun (Ty.fn [x.output] (.list v.event))) :
    runQuery T (a.ownFront xs) x caller input onAnswer = (runQuery T a x caller input onAnswer).map (Acc.ownFront xs) := by
  unfold runQuery
  rw [show execQuery (a.ownFront xs).state x caller input = execQuery a.state x caller input from rfl]
  split
  · rfl
  · exact applyEvents_own T xs _ { a with state := { a.state with fresh := a.state.fresh + 1 } }

theorem runOwn_own (T : List TypeDecl) (xs : List (EffectV v.event)) (a : Acc v) (eff : EffectV v.event) :
    runOwn T (a.ownFront xs) eff = (runOwn T a eff).map (Acc.ownFront xs) := by
  cases eff with
  | request => rfl
  | command name c i j caller value onAnswer =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    cases oc with
    | none => rfl
    | some hc =>
      generalize ownCommand (v := v) name i j = ox
      cases ox with
      | none => rfl
      | some x =>
        obtain ⟨hc⟩ := hc
        obtain ⟨x, hi, hj⟩ := x
        exact runCommand_own T xs a x _ _ _
  | query name c i o caller value onAnswer =>
    unfold runOwn
    dsimp only
    generalize Ty.same c v.caller = oc
    cases oc with
    | none => rfl
    | some hc =>
      generalize ownQuery (v := v) name i o = ox
      cases ox with
      | none => rfl
      | some x =>
        obtain ⟨hc⟩ := hc
        obtain ⟨x, hi, ho⟩ := x
        exact runQuery_own T xs a x _ _ _

variable (T : List TypeDecl)

/-- Runs the own effects of `a.own` from the place `k` on, one internal step each, keeping every effect in the queue;
an effect at a place past `fuel` internal steps is a fault. -/
def settleFrom : Nat → Nat → Acc v → Except Fault (Acc v)
  | fuel, k, a => match a.own[k]?, fuel with
    | none, _ => .ok a
    | some _, 0 => .error .cascadeLimit
    | some eff, f + 1 => do settleFrom f (k + 1) (← runOwn T a eff)

theorem settle_from : (fuel k : Nat) → (a : Acc v) →
    settle T fuel { a with own := a.own.drop k } = (settleFrom T fuel k a).map fun a => { a with own := [] }
  | fuel, k, a => by
    unfold settle settleFrom
    cases hk : a.own[k]? with
    | none =>
      have : a.own.drop k = [] := List.drop_eq_nil_of_le (by simpa using hk)
      simp [this, Except.map]
    | some eff =>
      have hlt : k < a.own.length := (List.getElem?_eq_some_iff.1 hk).1
      have hd : a.own.drop k = eff :: a.own.drop (k + 1) := by
        rw [List.drop_eq_getElem_cons hlt, (List.getElem?_eq_some_iff.1 hk).2]
      simp only [hd]
      cases fuel with
      | zero => rfl
      | succ f =>
        simp only
        have h1 : ({ { a with own := eff :: a.own.drop (k + 1) } with own := a.own.drop (k + 1) } : Acc v) =
            Acc.ownFront (a.own.drop (k + 1)) { a with own := [] } := by simp [Acc.ownFront]
        have h2 : a = Acc.ownFront a.own { a with own := [] } := by simp [Acc.ownFront]
        rw [h1, runOwn_own]
        conv => rhs; rw [h2, runOwn_own]
        cases runOwn T { a with own := [] } eff with
        | error e => rfl
        | ok c =>
          simp only [Except.map, bind, Except.bind]
          have ih := settle_from f (k + 1) (Acc.ownFront a.own c)
          rw [show (Acc.ownFront a.own c).own.drop (k + 1) = a.own.drop (k + 1) ++ c.own by
            simp [Acc.ownFront, List.drop_append_of_le_length (Nat.succ_le_of_lt hlt)]] at ih
          exact ih

/-- `settle` is `settleFrom` from the queue's first place. -/
theorem settle_eq_from (fuel : Nat) (a : Acc v) :
    settle T fuel a = (settleFrom T fuel 0 a).map fun a => { a with own := [] } := by
  simpa using settle_from T fuel 0 a

end Step

end Tazuna.Ir
