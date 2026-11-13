import Tazuna.Thm.Verify.Complete.Top
import Tazuna.Thm.Verify.Complete.Subscriptions

/-!
The invariant of the states before the windows of a quiet comparison, and what each quiet window and pair of `in` lines
gives.
-/

namespace Tazuna.Thm.Verify.Complete.Induction

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Ids Tazuna.Thm.Verify.Complete.Lists
open Tazuna.Thm.Verify.Complete.Search Tazuna.Thm.Verify.Complete.Window Tazuna.Thm.Verify.Complete.Run
open Tazuna.Thm.Verify.Complete.Steps Tazuna.Thm.Verify.Complete.Subscriptions Tazuna.Thm.Verify.Complete.Top

/-- The subscriptions open before window `k`. -/
def openBefore (ws : List Window) (k : Nat) : List (String × Subscription) :=
  (ws.take k).foldl (fun o w => follow o (w.before.filter (·.line.isSubscribing))) []

/-- The createKey values that the `out` lines before window `k` create. -/
def declaredBefore (ws : List Window) (k : Nat) : List String :=
  (ws.take k).flatMap fun w => w.before.flatMap (·.line.created.getD [])

/-- Implementation subscription `t` was paired in window `j` with an open snapshot subscription alike `s`. -/
def SubscribedAt (E : List Window) (Q : Nat → List (String × String)) (j : Nat) (s t : String) : Prop :=
  ∃ o a b, (o, t) ∈ Q j ∧ (openAfter E j).lookup s = some a ∧ (openAfter E j).lookup o = some b ∧
    alike a.out.line b.out.line = true

/-- The invariant of the state before window `k`. -/
structure Inv (S : List (Option Line)) (A : List Window) (Q : Nat → List (String × String)) (k : Nat) (st : St) :
    Prop where
  reportedM : st.reportedMissing = []
  reportedU : st.reportedUnexpected = []
  idsWf : IdsWf st.ids
  oneToOne : OneToOne st.keys
  keysSnap : ∀ u ∈ st.keys, ∃ l, some l ∈ S ∧ u.snapshot ∈ l.created.getD []
  declared : st.declared = declaredBefore (steps S) k
  openS : st.openSnapshot = openBefore (steps S) k
  openT : st.openTrace = openBefore A k
  subs : ∀ s ids, st.subscriptionIds.lookup s = some ids → ∀ t ∈ ids, ∃ j < k, SubscribedAt (steps S) Q j s t

theorem Inv.zero (S : List (Option Line)) (A : List Window) (Q : Nat → List (String × String)) :
    Inv S A Q 0 {} :=
  ⟨rfl, rfl, IdsWf.empty, by simp [OneToOne], by simp, by simp [declaredBefore], by simp [openBefore],
    by simp [openBefore], by simp⟩

theorem openBefore_succ (ws : List Window) (k : Nat) (w : Window) (hw : ws[k]? = some w) :
    openBefore ws (k + 1) = follow (openBefore ws k) (w.before.filter (·.line.isSubscribing)) := by
  unfold openBefore
  rw [List.take_add_one, hw]
  simp

theorem declaredBefore_succ (ws : List Window) (k : Nat) (w : Window) (hw : ws[k]? = some w) :
    declaredBefore ws (k + 1) = declaredBefore ws k ++ w.before.flatMap (·.line.created.getD []) := by
  unfold declaredBefore
  rw [List.take_add_one, hw]
  simp

theorem foldl_created (L : List Out) (d : List String) :
    L.foldl (fun d s => d ++ s.line.created.getD []) d = d ++ L.flatMap (·.line.created.getD []) := by
  induction L generalizing d with
  | nil => simp
  | cons a L ih => simp [ih]

theorem mem_declaredBefore {S : List (Option Line)} {k : Nat} {x : String} (h : x ∈ declaredBefore (steps S) k) :
    ∃ l, some l ∈ S ∧ x ∈ l.created.getD [] := by
  obtain ⟨w, hw, hx⟩ := List.mem_flatMap.mp h
  obtain ⟨o, ho, hx⟩ := List.mem_flatMap.mp hx
  exact ⟨o.line, (before_atLine S (List.mem_of_mem_take hw) ho).mem, hx⟩

theorem renameBy_eq (d : List String) (ws : List Window) (k : Nat) (hd : d = declaredBy ws k) (R : Renaming) :
    renameBy d R = keysAt R.traceOf? ws k := by
  funext x
  subst hd
  simp [renameBy, keysAt]


/-- The subscription pairings of the windows' searches. -/
def subsOf (c : Ctx) (E A : List Window) (j : Nat) : List (String × String) := (pairingAt c E A j).subscriptions

/-- What a quiet window `k` gives, with `st` the state before it and `p` the pairing of its search. -/
structure WindowStep (S : List (Option Line)) (A : List Window) (internal : Line → Bool) (k : Nat) (e a : Window)
    (st W : St) (p : Pairing) : Prop where
  inv : Inv S A (subsOf (context S internal) (steps S) A) (k + 1) W
  keys : W.keys = p.keys
  ids : W.ids = p.ids
  ok : WindowOK (scopeOf (context S internal) (enter st e.before a.before) a.before) (pairedOut internal e)
    st.ids st.keys p
  declared : (enter st e.before a.before).declared = declaredBy (steps S) k
  openS : (enter st e.before a.before).openSnapshot = openAfter (steps S) k
  openT : (enter st e.before a.before).openTrace = openAfter A k

theorem window_step (S : List (Option Line)) (A : List Window) (internal : Line → Bool) (k : Nat) (e a : Window)
    (he : (steps S)[k]? = some e) (ha : A[k]? = some a)
    (hinv : Inv S A (subsOf (context S internal) (steps S) A) k (stateAt (context S internal) (steps S) A k))
    (h1 : (runWindow (context S internal) (stateAt (context S internal) (steps S) A k) (befores (steps S) k)
      (befores A k) (prevAt A k) (prevAt (steps S) k)).1 = [])
    (h2 : (runWindow (context S internal) (stateAt (context S internal) (steps S) A k) (befores (steps S) k)
      (befores A k) (prevAt A k) (prevAt (steps S) k)).2.1 = none) :
    WindowStep S A internal k e a (stateAt (context S internal) (steps S) A k)
      (windowRun (context S internal) (steps S) A k (stateAt (context S internal) (steps S) A k))
      (pairingAt (context S internal) (steps S) A k) := by
  generalize hc : context S internal = c at *
  generalize hst : stateAt c (steps S) A k = st at *
  have hbe : befores (steps S) k = e.before := by simp [befores, he]
  have hba : befores A k = a.before := by simp [befores, ha]
  obtain ⟨p, hp, hW⟩ := window_paired c st (befores (steps S) k) (befores A k) _ _ hinv.reportedM hinv.reportedU h1 h2
  have hWr : windowRun c (steps S) A k st = _ := hW
  clear hW
  rw [hbe, hba] at hp hWr
  have hpa : pairingAt c (steps S) A k = p := by
    unfold pairingAt
    simp only [hst, hbe, hba, hp]
  rw [hpa, hWr]
  have ok := window_ok (specOut := comparedOut c e.before) hp
  subst hc
  have hcomp : comparedOut (context S internal) e.before = pairedOut internal e := rfl
  rw [hcomp] at ok
  have F := ok.frame
  have hdecl : (enter st e.before a.before).declared = declaredBy (steps S) k := by
    simp only [enter, foldl_created, hinv.declared, declaredBy]
    exact (declaredBefore_succ (steps S) k e he).symm
  have hos : (enter st e.before a.before).openSnapshot = openAfter (steps S) k := by
    simp only [enter, hinv.openS]
    exact (openBefore_succ (steps S) k e he).symm
  have hot : (enter st e.before a.before).openTrace = openAfter A k := by
    simp only [enter, hinv.openT]
    exact (openBefore_succ A k a ha).symm
  refine ⟨⟨hinv.reportedM, hinv.reportedU, F.idsWf hinv.idsWf, F.oneToOne hinv.oneToOne, fun u hu => ?_, hdecl,
    hos, hot, ?_⟩, rfl, rfl, ok, hdecl, hos, hot⟩
  · rcases F.declared u hu with h | h
    · exact hinv.keysSnap u h
    · have : u.snapshot ∈ declaredBy (steps S) k := by
        have := h; simp only [scopeOf] at this; rw [hdecl] at this; simpa using this
      exact mem_declaredBefore this
  · refine subscribed_inv _ _ _ _ (fun s ids hl t ht => ?_) (fun s other t sa sb hm hs ho hal => ?_)
    · obtain ⟨j, hj, hsub⟩ := hinv.subs s ids hl t ht
      exact ⟨j, by omega, hsub⟩
    · refine ⟨k, by omega, other, sa, sb, ?_, ?_, ?_, hal⟩
      · simp only [subsOf, hpa]; exact hm
      · simp only [scopeOf] at hs; rw [hos] at hs; exact hs
      · simp only [scopeOf] at ho; rw [hos] at ho; exact ho


theorem input_step {S : List (Option Line)} {A : List Window} {Q : Nat → List (String × String)} {k : Nat} {c : Ctx}
    {W : St} (hinv : Inv S A Q k W) {s t : Out} {p : Pairing} (h : sameInput (inputScope c W) W s t = .paired p) :
    Inv S A Q k { W with ids := p.ids, keys := p.keys } ∧ InputOK W s t p := by
  have I := input_ok h
  refine ⟨⟨hinv.reportedM, hinv.reportedU, I.idsWf hinv.idsWf, I.oneToOne hinv.oneToOne, fun u hu => ?_,
    hinv.declared, hinv.openS, hinv.openT, hinv.subs⟩, I⟩
  rcases I.declared u hu with h | h
  · exact hinv.keysSnap u h
  · rw [hinv.declared] at h
    exact mem_declaredBefore (by simpa using h)

end Tazuna.Thm.Verify.Complete.Induction
