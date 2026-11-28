import Tazuna.Cli.Prove

/-! Where a service's script bytes go: for each input kind, the bytes of its bound question as prove sends it, and the
share of each part of its step (the input's own stage, each cascade place and own kind, the step's end, the
condition's parts); for the service, the bytes of each response, timer and own-pair question. A part's share is its
printed size with every shared term counted once, the first time a part in this order uses it, so the shares add up
to about the whole. A development tool: it reads the encoder's terms and prints one JSON line per row. -/

namespace Tazuna.Cli

open Lean (Json)
open Tazuna.Ir Tazuna.Smt

private def kids : Term → List Term
  | .not a | .len a | .is _ _ a | .sel _ _ _ a => [a]
  | .and a b | .or a b | .eq a b | .lt a b | .le a b | .add a b | .sub a b | .mul a b | .div a b | .mod a b
  | .cat a b | .slt a b => [a, b]
  | .ite c a b => [c, a, b]
  | .ctor _ _ args | .app _ args => args
  | _ => []

private def opBytes : Term → Nat
  | .var n => 1 + (toString n).length
  | .int n => (toString n).length + (if n < 0 then 4 else 0)
  | .str s => s.length + 2
  | .bool b => if b then 4 else 5
  | .ref i => 1 + (toString i).length
  | .not _ | .and .. | .ite .. | .div .. | .mod .. => 3
  | .or .. | .le .. | .app .. => 2
  | .eq .. | .lt .. | .add .. | .sub .. | .mul .. => 1
  | .len .. => 7 | .cat .. => 6 | .slt .. => 5 | .ctor .. => 5 | .is .. => 12 | .sel .. => 8 | .shared .. => 0

/-- Printed bytes of `t` beyond the shared terms in `seen`, each shared term with its definition counted once. -/
private partial def dag (t : Term) (seen : Std.HashSet UInt64) : Nat × Std.HashSet UInt64 :=
  match t with
  | .shared h b =>
    if seen.contains h then (5, seen)
    else
      let (n, seen) := dag b (seen.insert h)
      (35 + n, seen)
  | t =>
    let ks := kids t
    ks.foldl (fun (acc, s) k => let (n, s) := dag k s; (acc + n + 1, s)) (opBytes t + (if ks.isEmpty then 0 else 2), seen)

private def eventsTerms {v : ServiceV} (e : EventsOut v) : List Term :=
  [e.records] ++ e.tables.toList ++ [e.nextId, e.queued] ++ e.news.flatMap (fun s => [s.flag, s.id, s.entry]) ++
    e.owns.flatMap (fun s => [s.flag, s.place, s.effect]) ++ e.events.flatMap (fun s => s.1 :: s.2.1)

private def kindName {v : ServiceV} : OwnKindOut v → String
  | .command n _ | .query n _ | .missing n => n

private def kindTerms {v : ServiceV} (tst : Term) : OwnKindOut v → List Term
  | .command _ o => [tst, o.callerOk, o.decided.ok, o.decided.rejection] ++ o.rules.map (·.2) ++
      o.decided.ensures.map (·.2) ++ eventsTerms o.decided.after ++ eventsTerms o.answered
  | .query _ o => [tst, o.callerOk] ++ o.rules.map (·.2) ++ eventsTerms o.answered
  | .missing _ => [tst]

/-- A step's parts in pipeline order: the input's own stage, each cascade place's own kinds and merged terms, the
step's end. -/
private def stages {v : ServiceV} (o : StepOut v) : List (String × List Term) :=
  let pre : List (String × List Term) := match o with
    | .event e => [("input", e.event :: eventsTerms e.after)]
    | .answer a => [("input", [a.hit, a.events] ++ a.rules.map (·.2) ++ eventsTerms a.after)]
    | .command c => [("input", [c.callerOk, c.decided.ok, c.decided.rejection] ++ c.rules.map (·.2) ++
        c.decided.ensures.map (·.2))]
    | .clock k => [("input", [k.forward, k.over])]
    | _ => []
  match o.finish? with
  | none => pre
  | some fo =>
    let terms (t : StepTerms v) := [t.fault, t.fresh] ++ eventsTerms t.done
    pre ++ (fo.settle.steps.zipIdx.flatMap fun ((act, os), j) =>
        (os.kinds.map fun (tst, k) => (s!"cascade {j} {kindName k}", kindTerms tst k)) ++
        [(s!"cascade {j}", act :: terms os.terms)]) ++
      [("settled", fo.settle.over :: terms fo.settle.terms), ("pending", [fo.pending]),
       ("invariants", fo.invariants.map (·.2))]

private def textBytes (ids : Option Nat) (q : TypedScript) : Nat :=
  match (Script.sent ids q.script).text [] with
  | some t => t.utf8ByteSize
  | none => 0

private def row (fields : List (String × Json)) : IO Unit := IO.println (Json.compress (Json.mkObj fields))

/-- One service's rows. -/
def partsOf (c : CheckedSpec) (sv : CheckedService c) : IO Unit := do
  let v := sv.v
  let L := sv.L
  let senv := sv.senv
  for inp in stepInputs v (shapes v) senv.nT (stateWidth v) do
    match stepAsk L c.T c.P v senv inp with
    | .error _ => row [("service", Json.str v.name), ("kind", Json.str inp.text), ("refused", Json.bool true)]
    | .ok a =>
      let st := stages a.t.out
      let parts := st ++ [("cond", [a.t.cond]), ("side", [a.side]), ("held", [a.held])]
      let shared := ShareCommon.shareCommon' (parts.map fun (_, ts) => allT ts)
      let mut seen : Std.HashSet UInt64 := {}
      let mut cols : List (String × Json) := []
      for ((name, _), t) in parts.zip shared do
        let (n, s) := dag t seen
        seen := s
        cols := cols ++ [(name, Lean.toJson n)]
      let dropped : List String := match a.t.out.finish? with
        | some fo => fo.settle.steps.zipIdx.flatMap fun ((st : Term × OwnStepOut v), j) =>
            (st.2.listed.filter fun (_, k) => !st.2.kinds.any fun (_, k') => kindName k' == kindName k).map
              fun (_, k) => s!"{j} {kindName k}"
        | none => []
      row ([("service", Json.str v.name), ("kind", Json.str inp.text), ("bound", Lean.toJson (textBytes L.ids a.bound)),
        ("dropped", Lean.toJson dropped)] ++ cols)
      for resp in v.responses do
        match respStep L resp inp a with
        | .ok q => row [("service", Json.str v.name), ("kind", Json.str inp.text),
            ("response", Json.str resp.name), ("bytes", Lean.toJson (textBytes L.ids q))]
        | .error _ => pure ()
  for m in v.machines do
    match timerQuestions L m with
    | .ok (q1, q2) => row [("service", Json.str v.name), ("timer", Json.str m.name),
        ("bytes", Lean.toJson (textBytes L.ids q1 + textBytes L.ids q2))]
    | .error _ => pure ()
  let owns := L.ownsOf v.event
  for (k1, k2) in L.ownPairs v.event do
    let ask := L.pairAsk c.P v senv k1 k2
    if ask = .none then
      row [("service", Json.str v.name), ("pair", Json.str (ownText owns owns[k1] ++ " then " ++ ownText owns owns[k2])),
        ("apart", Json.bool true), ("bytes", Lean.toJson 0)]
      continue
    match pairQuestions L c.T c.P v senv k1 k2 with
    | .ok (q1, q2) => row [("service", Json.str v.name),
        ("pair", Json.str (ownText owns owns[k1] ++ " then " ++ ownText owns owns[k2])),
        ("bytes", Lean.toJson (textBytes L.ids q1 + if ask = .bound then 0 else textBytes L.ids q2))]
    | .error _ => pure ()

end Tazuna.Cli
