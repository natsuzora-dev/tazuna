import Tazuna.Semantics.Step

/-! One example per step rule, on a small service: the records are a running total, a command adds a positive amount
below 100, the total stays under 50, and a machine waits 10 ms after the total first moves, then pings an external
whose answer adds 1. -/

namespace Tazuna.Ir.StepExamples

open Step

private def I (x : Int) : Int := x
private def rule (n : String) (b : Bool) : Ty.rules.den0 := [(n, Ty.ofBool b, ())]

def ping : EffectV .int :=
  { external := "mail", command := "ping", input := .str, output := .int, rejection := .str, value := "hi",
    onAnswer := fun (a, ()) => match a with
      | .inl _ => [(1 : Int)]
      | .inr _ => [] }

def watch : MachineV .int .int :=
  { name := "watch", key := .int, state := .int,
    instances := fun (r, ()) => if 0 < I r then [(0 : Int)] else [],
    initial := (0 : Int),
    on := fun (_, st, _, _, _, ()) => .inr (.inl (I st + 1, ())),
    after := fun (_, st, _, _, ()) => if I st = 1 then .inl (.inl ((10 : Int), (5 : Int), ()), ()) else .inr (.inl ()),
    effect := fun _ st _ _ => if I st = 5 then some ping else none,
    invariants := fun _ => [] }

def add : CommandV .int .int .int :=
  { name := "add", input := .int, rejection := .str, callers := [(1 : Int)],
    accepts := fun (i, ()) => rule "small" (decide (I i < 100)),
    decide := fun (.inl (_, i, _, _, _, ()), ()) =>
      if 0 < I i then .inl ([i], ()) else .inr (.inl ("positive", ())),
    ensures := fun (.inl (r, _, _, _, _, ()), r', ()) => rule "grows" (decide (I r ≤ I r')) }

def total : QueryV .int .int :=
  { name := "total", input := .int, output := .int, callers := [(1 : Int)], accepts := fun _ => [],
    resolve := fun (.inl (r, _, _, _, _, ()), ()) => r }

def svc : ServiceV :=
  { name := "sum", records := .int, event := .int, caller := .int, init := (0 : Int),
    apply := fun (r, e, ()) => I r + I e,
    subscribes := [{ source := "peer", name := "moved", event := .int, wrap := fun (x, ()) => x }],
    commands := [add], queries := [total], machines := [watch], reactions := [],
    invariants := fun (r, ()) => rule "under 50" (decide (I r < 50)), responses := [],
    bounds := { creates := [], items := 3, cascade := 2, steps := 5 } }

def s0 : State svc := State.init svc
def cmd (caller amount : Int) : Input svc := .command ⟨0, by decide⟩ caller amount
def summary (s : State svc) (i : Input svc) : String := (step svc s i).outcome.summary
def after (s : State svc) (is : List (Input svc)) : State svc := (run svc s is).1

-- A command from a caller outside `callers`, or with input breaking `accepts`, is Invalid without deciding.
#guard summary s0 (cmd 2 5) == "invalid [callers]"
#guard summary s0 (cmd 1 500) == "invalid [small]"
-- `decide` rejects, or accepts with its events.
#guard summary s0 (cmd 1 0) == "rejected"
#guard summary s0 (cmd 1 5) == "accepted 1"
-- An invariant broken after the step is a fault, and the state stays as it was.
#guard summary s0 (cmd 1 60) == "fault invariant under 50"
#guard I (step svc s0 (cmd 1 60)).state.records == 0
-- A query answers from the records.
#guard summary (after s0 [cmd 1 5]) (.query ⟨0, by decide⟩ (1 : Int) (0 : Int)) == "answered"
-- A peer event arrives as one of the service's events.
#guard I (after s0 [.event ⟨0, by decide⟩ (7 : Int)]).records == 7
-- The first event starts the machine's instance; the next enters state 1, which sets a timer for 10 ms later.
#guard (after s0 [cmd 1 5]).machines.map (·.2.map (·.timer.isSome)) == [[false]]
#guard (after s0 [cmd 1 5, cmd 1 1]).machines.map (·.2.map (·.timer.map (·.1))) == [[some 10]]
-- A clock line before the deadline fires nothing; at it, the instance enters 5, whose effect sends a request.
#guard (step svc (after s0 [cmd 1 5, cmd 1 1]) (.clock 9)).out.length == 0
#guard (step svc (after s0 [cmd 1 5, cmd 1 1]) (.clock 10)).out.map (·.command) == ["ping"]
-- Time does not move back.
#guard summary (after s0 [.clock 5]) (.clock 4) == "invalid [time moves forward]"
-- The answer to the pending request becomes events; an answer to no pending request is a fault.
#guard summary (after s0 [cmd 1 5, cmd 1 1, .clock 10]) (.answer 0 ⟨Ty.result .int .str, .inl ((0 : Int), ())⟩) ==
  "accepted 1"
#guard summary s0 (.answer 0 ⟨Ty.result .int .str, .inl ((0 : Int), ())⟩) == "fault answerUnmatched 0"
-- An answer of the wrong type matches no request.
#guard summary (after s0 [cmd 1 5, cmd 1 1, .clock 10]) (.answer 0 ⟨.int, (0 : Int)⟩) == "fault answerUnmatched 0"
-- A step with more events than the cascade bound is a fault.
def tight : ServiceV := { svc with bounds := { svc.bounds with cascade := 0 } }
#guard (step tight (State.init tight) (.event ⟨0, by decide⟩ (1 : Int))).outcome.summary == "fault cascadeLimit"
-- Every input has one outcome.
#guard (run svc s0 [cmd 1 5, cmd 2 5, .clock 3]).2.length == 3

end Tazuna.Ir.StepExamples
