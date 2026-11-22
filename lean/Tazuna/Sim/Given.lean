import Tazuna.Service.Integrity
import Tazuna.Sim.Network

/-!
Given arranges the world before the startup: the roles that it lists, and each running service at the start with its
records. What Given gets wrong is reported before anything begins.
-/

namespace Tazuna.Sim

open Tazuna.Data Tazuna.Service
open Tazuna.Scenario (GivenRecord Peer)

/--
The services that the own service `own` exchanges messages with: those whose definitions its definitions name, and the
spec services whose definitions name its definitions, in code-point order.
-/
def staticPeers (j : Spec.Structure) (own : String) : List String :=
  let named (d : Spec.Definition) : List Spec.Ref :=
    match d.body with
    | .automation a => [a.receives, a.command]
    | .machine c | .screen c => (c.receives ++ c.commands ++ c.queries ++ c.screens).map (·.2)
    | _ => []
  let external (s : String) := j.services.any fun i => i.name == s && i.external
  let found := j.definitions.flatMap fun d =>
    (named d).filterMap fun r =>
      if r.service == d.service then none
      else if d.service == own then some r.service
      else if r.service == own && !external d.service then some d.service
      else none
  found.eraseDups.mergeSort fun a b => decide (a ≤ b)

/-- The peers of Given by service, each from its first entry; an entry of the own service is none. -/
def peersOf (sc : Scenario) : List (String × Peer) :=
  sc.given.peers.foldl (init := []) fun ps p =>
    if p.service == sc.service || ps.any (·.1 == p.service) then ps else ps ++ [(p.service, p.peer)]

/-- The services that run in `sc`: the own service, then each running peer of Given. -/
def runningOf (sc : Scenario) : List String :=
  sc.service :: (peersOf sc).filterMap fun (s, p) => match p with
    | .run _ => some s
    | _ => none

/--
The world before the startup with the running services `services`: the roles that Given lists, and each running service
at the start, whose name qualifies its createKey values.
-/
def World.startWith (sc : Scenario) (services : List (String × Service)) : World :=
  let roles := (sc.service, Role.own) :: (peersOf sc).map fun (s, p) => (s, match p with
    | .run _ => Role.run
    | .external => .external
    | .skip _ => .skip)
  let now := sc.given.start
  { now, roles, services, states := (runningOf sc).map fun s => (s, { now, service := s }) }

/-- The world before the startup: World.startWith with each running service of the structure `j`. -/
def World.start {m : Type → Type} [Monad m] [MonadNote m] (j : Spec.Structure) (sc : Scenario) : m World := do
  pure (World.startWith sc (← (runningOf sc).mapM fun s => do pure (s, ← Service.ofStructure j s)))

/-- The records that Given writes for the running service `service`, in written order. -/
def writtenRecords (sc : Scenario) (service : String) : List GivenRecord :=
  if service == sc.service then sc.given.records
  else match (peersOf sc).lookup service with
    | some (.run records) => records
    | _ => []

/-- Whether the key `a` comes before `b`: none first, then in code-point order. -/
def keyBefore : Option String → Option String → Bool
  | none, _ => true
  | some _, none => false
  | some x, some y => decide (x ≤ y)

/-- Whether the Given record `a` comes before `b`: by entity in code-point order, then by key. -/
def recordBefore (a b : GivenRecord) : Bool :=
  if a.entity = b.entity then keyBefore a.key b.key else decide (a.entity ≤ b.entity)

/--
The records that Given writes for the running service `service`, ordered by recordBefore: Given writes the
records of an entity as a bag, so the order they are written in reaches nothing.
-/
def givenRecords (sc : Scenario) (service : String) : List GivenRecord :=
  (writtenRecords sc service).mergeSort recordBefore

/--
The first string of `v` of the form `<service>/<e>-<n>` of a key of the keyed entity `e` that the running
running service creates, with the entity.
-/
def World.writtenKey? (w : World) (v : Value) : Option (String × Spec.Ref) :=
  v.strings.findSome? fun x => (w.keyEntity? x).map (x, ·)

variable {m : Type → Type} [Monad m] [MonadNote m]

/--
Given's records of `service` as rows, each parsed by its entity's schema, with a violation for each that is invalid,
write a created key that `written` finds, or clash with an earlier one, which no row holds.
-/
def givenRows (st : Service) (fs : Functions m) (written : Value → Option (String × Spec.Ref)) (service : String)
    (records : List GivenRecord) : m (Records × List InvalidScenario) :=
  records.foldlM (init := ([], [])) fun (rows, found) g => do
    let invalid := (rows, found ++ [InvalidScenario.invalidRecord service g.entity g.key])
    if !st.entities.contains g.entity || st.singles.contains g.entity != g.key.isNone then return invalid
    if let some (key, e) := written (.arr ((g.key.map Value.str).toList ++ [g.value])) then
      return (rows, found ++ [.writtenGivenKey service g.entity g.key key e])
    match ← fs.parseOutside st (.record (st.ref g.entity)) g.value with
    | .ok (some value) =>
      let row : Row := { entity := g.entity, key := g.key, value }
      if rows.any (clash st · row) then return (rows, found ++ [.duplicateRecord service g.entity g.key])
      pure (rows ++ [row], found)
    | _ => pure invalid

/-- The violations of the entity invariants of each row and of the service invariants that fail on `rows`. -/
def givenInvariants (fs : Functions m) (service : String) (rows : Records) : m (List InvalidScenario) := do
  let each ← rows.mapM fun r => do
    pure (match ← fs.invariant r.entity r.value with
      | .ok none => []
      | .ok (some c) => [InvalidScenario.brokenGivenInvariant service (some r.entity) r.key (some c)]
      | .error _ => [.brokenGivenInvariant service (some r.entity) r.key none])
  let whole := match ← fs.serviceInvariant rows with
    | .ok none => []
    | .ok (some c) => [InvalidScenario.brokenGivenInvariant service none none (some c)]
    | .error _ => [.brokenGivenInvariant service none none none]
  pure (each.flatten ++ whole)

/--
The world with each running service's Given records, or with what Given gets wrong: a peer listed twice or the own
service listed as one, a peer of the static peer list left out, and for each running service, invalid or clashing
records, records that write a created key, a single entity without a record, and else failing invariants.
-/
def World.given (w : World) (j : Spec.Structure) (fsOf : String → Functions m) (sc : Scenario) : m World := do
  let listed := sc.given.peers.map (·.service)
  let repeated := (listed.zipIdx.filter fun (p, k) => p == sc.service || (listed.take k).contains p).map fun (p, _) =>
    InvalidScenario.repeatedPeer p
  let unlisted := ((staticPeers j sc.service).filter fun s => !listed.contains s).map InvalidScenario.unlistedPeer
  let w := (repeated ++ unlisted).foldl World.note w
  w.services.foldlM (init := w) fun w (service, st) => do
    let fs := fsOf service
    let records := givenRecords sc service
    let (rows, invalid) ← givenRows st fs w.writtenKey? service records
    let missing := (st.singles.filter fun e => !records.any (·.entity == e)).map (InvalidScenario.missingRecord service ·)
    let broken ← if invalid.isEmpty && missing.isEmpty then givenInvariants fs service rows else pure []
    let w := (invalid ++ missing ++ broken).foldl World.note w
    pure { w with states := w.states.map fun (q, s) =>
      if q == service then (q, { s with records := rows }) else (q, s) }

end Tazuna.Sim
