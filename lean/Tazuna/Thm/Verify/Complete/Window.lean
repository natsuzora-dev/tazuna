import Tazuna.Thm.Verify.Complete.Search

/-!
The comparison of one window: a window whose search finds no pairing is reported, and a quiet window keeps the pairing
of its search.
-/

namespace Tazuna.Thm.Verify.Complete.Window

open Tazuna.Data Tazuna.Verify Tazuna.Thm.Verify.Compare Tazuna.Thm.Verify.Matching
open Tazuna.Thm.Verify.Complete.Values Tazuna.Thm.Verify.Complete.Ids Tazuna.Thm.Verify.Complete.Lists
open Tazuna.Thm.Verify.Complete.Search

/-- The state in which compareWindow searches. -/
def enter (st : St) (specOut traceOut : List Out) : St :=
  { st with findings := []
            declared := specOut.foldl (fun d s => d ++ s.line.created.getD []) st.declared
            window := st.window + 1
            openSnapshot := follow st.openSnapshot (specOut.filter (·.line.isSubscribing))
            openTrace := follow st.openTrace (traceOut.filter (·.line.isSubscribing)) }

/-- The scope of compareWindow's search. -/
def scopeOf (c : Ctx) (st : St) (traceOut : List Out) : Scope :=
  { ctx := c, declared := st.declared, window := st.window,
    traceOut := traceOut.filter fun t => !t.line.isSubscribing && !c.internal t.line,
    openSnapshot := st.openSnapshot, openTrace := st.openTrace }

def comparedOut (c : Ctx) (specOut : List Out) : List Out :=
  specOut.filter fun s => !s.line.isSubscribing && !c.internal s.line

def goalsOf (c : Ctx) (st : St) (specOut : List Out) : List Goal :=
  (byRank (comparedOut c specOut)).map .out ++ st.openSnapshot.map (.subscription ·.1)

set_option linter.unusedSimpArgs false in
theorem runWindow_eq (c : Ctx) (st : St) (specOut traceOut : List Out) (m s : Nat) :
    runWindow c st specOut traceOut m s =
      let st₁ := enter st specOut traceOut
      let sc := scopeOf c st₁ traceOut
      match pairAll sc (goalsOf c st₁ specOut) { ids := st₁.ids, keys := st₁.keys } with
      | .paired p =>
        ([], none, { st₁ with ids := p.ids, keys := p.keys,
                              subscriptionIds := explain.subscribed sc st₁.subscriptionIds p.subscriptions })
      | .limited => ([], some (.searchLimit m s), st₁)
      | .unpaired =>
        let r := ((explain sc (comparedOut c specOut) m).run c).run st₁
        (r.2.findings, none, r.2) := by
  simp only [runWindow, compareWindow, bind, StateT.bind, ReaderT.bind, read, ReaderT.read, get, getThe,
    MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, set, StateT.set,
    MonadStateOf.set, pure, StateT.pure, ReaderT.pure, Functor.map, StateT.map, MonadReaderOf.read,
    MonadReader.read, MonadState.get, MonadState.set, liftM, monadLift, MonadLift.monadLift, ReaderT.run, StateT.run,
    StateT.lift, Id.run, readThe, enter, scopeOf, goalsOf, comparedOut]
  generalize pairAll _ _ _ = o
  cases o <;> rfl

end Tazuna.Thm.Verify.Complete.Window
