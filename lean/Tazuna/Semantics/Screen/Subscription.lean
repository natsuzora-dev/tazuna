import Tazuna.Semantics.Chart.Exit

namespace Tazuna.Semantics

open Tazuna.Data

variable {m : Type → Type}

structure Wanted where
  slot : String
  activity : Activity
  input : Value
deriving DecidableEq, Repr, Inhabited

def setWanted (wanted : List Wanted) (w : Wanted) : List Wanted :=
  if wanted.any (·.slot == w.slot) then wanted.map fun x => if x.slot == w.slot then w else x
  else wanted ++ [w]

/--
The shows of the active states of `i` that apply: as with offers (innermostOffers), a state's shows of a slot does not
apply while an active descendant shows the same slot, as in SCXML, where a descendant's transition wins over an
ancestor's. Of two active states in parallel regions that show one slot, the later in document order wins (setWanted).
-/
def appliedShows (i : Instance) : List (String × Activity) :=
  let shows := (i.chart.states.filter (i.isIn ·.name)).flatMap fun cs =>
    (cs.activities.filter (·.keyword == "shows")).map (cs.name, ·)
  shows.filter fun (n, a) => !shows.any fun (d, b) => b.key == a.key && d != n && i.chart.tree.isDescendant d n

def wantedShows [Monad m] (st : Service) (fs : Functions m) (s : State) (i : Instance) :
    m (Except Fault (List Wanted)) :=
  (appliedShows i).foldlM (fun (acc : Except Fault (List Wanted)) (n, a) => do
    match acc with
    | .error v => pure (.error v)
    | .ok wanted =>
      match ← fs.showInput (s.scopeOf i (some n)) s.records a with
      | .error e =>
        pure (.error (issueViolation st (st.ref i.chart.name) e fun _ =>
          .showsInputSchema (st.ref i.chart.name) a.key))
      | .ok input => pure (.ok (setWanted wanted { slot := a.key, activity := a, input }))) (.ok [])

def inputOf (wanted : List Wanted) (slot : String) : Option Value := (wanted.find? (·.slot == slot)).map (·.input)

def State.endShowStep (wanted : List Wanted) (owner : String) (s : State) (p : Pending) : State :=
  let slot := p.requester.slot?.getD ""
  if (inputOf wanted slot).any (· == p.input) then s else
  let s := s.endSubscription p
  if (inputOf wanted slot).isNone then s.setShown owner slot .null else s

def State.subscribeStep (opened : List Pending) (owner : String) (s : State) (w : Wanted) : State :=
  if opened.any (fun p => p.requester.slot? == some w.slot && p.input == w.input) then s else
  s.await (.subscribe w.activity.target w.input) (.slot owner w.slot) w.activity w.input

def State.syncShows (s : State) (owner : String) (wanted : List Wanted) : State :=
  wanted.foldl (State.subscribeStep (s.openShows owner) owner)
    ((s.openShows owner).foldl (State.endShowStep wanted owner) s)

def refresh [Monad m] (st : Service) (fs : Functions m) (s : State) (owner : String) : m State := do
  match s.machine? owner with
  | none => pure s
  | some i =>
    if i.closed then pure s else
    match ← wantedShows st fs s i with
    | .error fault => pure (s.report (.fault fault))
    | .ok wanted => pure (s.syncShows owner wanted)

def refreshScreens [Monad m] (st : Service) (fs : Functions m) (s : State) : m State :=
  s.machines.foldlM (fun s i => if s.halted.isSome || !i.chart.screen then pure s else refresh st fs s i.resource) s

end Tazuna.Semantics
