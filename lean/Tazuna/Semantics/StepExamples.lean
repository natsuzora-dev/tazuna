import Tazuna.Semantics.Builtin
import Tazuna.Semantics.Step

/-! One example per step rule, on a small service: the records are a running total, a command adds a positive amount
below 100, the total stays under 50, and a machine waits 10 ms after the total first moves, then pings an external
whose answer adds 1. -/

namespace Tazuna.Ir.StepExamples

open Step

private def I (x : Int) : Int := x
private def rule (n : String) (b : Bool) : Ty.rules.den0 := [(n, Ty.ofBool b, ())]

/-- Named rules with one rule. -/
private def ruleE {Γ : List Ty} (n : String) (b : Expr [] Γ Ty.bool) : Expr [] Γ Ty.rules :=
  .list (.cons (.tuple (.cons (.str n) (.cons b .nil))) .nil)
private def recordsE {Γ : List Ty} (x : Expr [] Γ (Ty.ctx .int .int .int)) : Expr [] Γ .int :=
  .field (ft := .int) "records" 0 (by simp) x
private def inputE {Γ : List Ty} (x : Expr [] Γ (Ty.ctx .int .int .int)) : Expr [] Γ .int :=
  .field (ft := .int) "input" 1 (by simp) x

def ping : EffectV .int := .request
  { name := "ping", input := .str, output := .int, rejection := some .str, value := "hi",
    holds := fun _ => [], onAnswer := fun (a, ()) => match a with
      | .inl _ => [(1 : Int)]
      | .inr _ => [] }

def watch : MachineV .int .int :=
  { name := "watch", key := .int, state := .int,
    instances := fun (r, ()) => if 0 < I r then [(0 : Int)] else [],
    initial := (0 : Int),
    on := fun (.inl (_, st, _, _, ()), _, ()) => .inr (.inl (I st + 1, ())),
    after := fun (.inl (_, st, _, _, ()), ()) => if I st = 1 then .inl (.inl ((10 : Int), (5 : Int), ()), ()) else .inr (.inl ()),
    effect := fun _ st _ _ => if I st = 5 then some ping else none,
    invariants := fun _ => [] }

def add : CommandV .int .int .int :=
  { name := "add", input := .int, rejection := .str, callers := [(1 : Int)],
    accepts := .closed (.lam (ruleE "small" (.bin .lt (.var .here) (.int 100)))),
    decide := .closed (.lam (.call (.prim .require [.list .int, .str] rfl)
      (.cons (.bin .lt (.int 0) (inputE (.var .here))) (.cons (.str "positive")
        (.cons (.lam (.ctor (i := 2) (args := [.list .int, .str]) ⟨0, by decide⟩
          (.cons (.list (.cons (inputE (.var .here)) .nil)) .nil))) .nil))))),
    ensures := .closed (.lam (ruleE "grows" (.bin .le (recordsE (.var .here)) (.var (.there .here))))) }

def total : QueryV .int .int :=
  { name := "total", input := .int, output := .int, callers := [(1 : Int)], accepts := .closed (.lam (.list .nil)),
    resolve := .closed (.lam (recordsE (.var .here))) }

def svc : ServiceV :=
  { name := "sum", records := .int, event := .int, caller := .int, init := (0 : Int),
    apply := .closed (.lam (.bin .add (.var .here) (.var (.there .here)))),
    subscribes := [{ source := "peer", name := "moved", event := .int, wrap := .closed (.lam (.var .here)) }],
    declares := [.command .int .int .int add, .query .int .int total],
    commands := [add], queries := [total], sources := [], machines := [watch], reactions := [], scenarios := [],
    invariants := .closed (.lam (ruleE "under 50" (.bin .lt (.var .here) (.int 50)))), responses := [],
    bounds := { creates := [], items := 3, cascade := 2, steps := 5 },
    declared := [("mail", .externalCommand "ping" .str .int .str)] }

def s0 : State svc := State.init svc
def cmd (caller amount : Int) : Input svc := .command ⟨0, by decide⟩ caller amount
def summary (s : State svc) (i : Input svc) : String := (step svc s i).outcome.summary
def after (s : State svc) (is : List (Input svc)) : State svc := (run svc s is).1

-- A command from a caller outside `callers`, or with input breaking `accepts`, is Invalid without deciding.
#guard summary s0 (cmd 2 5) == "invalid [callers]"
#guard summary s0 (cmd 1 500) == "invalid [small]"
-- `decide` rejects, or accepts with its events.
#guard summary s0 (cmd 1 0) == "rejected"
#guard summary s0 (cmd 1 5) == "accepted"
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
#guard (step svc (after s0 [cmd 1 5, cmd 1 1]) (.clock 10)).out.map (·.name) == ["ping"]
-- Time does not move back.
#guard summary (after s0 [.clock 5]) (.clock 4) == "invalid [time moves forward]"
-- The answer to the pending request becomes events; an answer to no pending request is a fault.
#guard summary (after s0 [cmd 1 5, cmd 1 1, .clock 10]) (.answer 0 ⟨Ty.result .int .str, .inl ((0 : Int), ())⟩) ==
  "accepted"
#guard summary s0 (.answer 0 ⟨Ty.result .int .str, .inl ((0 : Int), ())⟩) == "fault answerUnmatched 0"
-- An answer of the wrong type matches no request.
#guard summary (after s0 [cmd 1 5, cmd 1 1, .clock 10]) (.answer 0 ⟨.int, (0 : Int)⟩) == "fault answerUnmatched 0"
-- A reaction sends the service's own `add` for some events: 7 adds 2, 1 adds 1 again and again, 3 adds 500.
def again : ReactionV .int .int :=
  { name := "again", react := fun e _ _ =>
      let send (n : Int) : EffectV .int := .command .int .int add (1 : Int) n fun _ => ([] : List Int)
      if I e = 7 then [send 2] else if I e = 1 then [send 1] else if I e = 3 then [send 500] else [] }
def loop : ServiceV := { svc with reactions := [again] }
def ev (x : Int) : Input loop := .event ⟨0, by decide⟩ x
-- The own command runs within the step: both events are applied.
#guard I (step loop (State.init loop) (ev 7)).state.records == 9
#guard ((step loop (State.init loop) (ev 7)).events.map I) == [7, 2]
-- An own command with input it does not accept is a fault, not Invalid.
#guard (step loop (State.init loop) (ev 3)).outcome.summary == "fault invalidEffect add [small]"
-- More internal steps than the cascade bound is a fault.
#guard (step loop (State.init loop) (ev 1)).outcome.summary == "fault cascadeLimit"
-- Two services that list the same command and query break the owner rule, once for each.
#guard ((SpecV.illegal prelude ⟨[svc, { svc with name := "other" }], []⟩).filter (·.1 == .owner)).length == 2
-- So does a service that declares an external's command.
#guard ((SpecV.illegal prelude ⟨[{ svc with declares := [.externalCommand "ping" .str .int .str] }], []⟩).filter
  (·.1 == .owner)).length == 1
/-- The outcome of the last of the inputs, run from the initial state. -/
def last (v : ServiceV) (is : List (Input v)) : String :=
  (((run v (State.init v) is).2.getLast?).map (·.outcome.summary)).getD ""
-- A request to a command no external declares is a fault.
def undeclared : ServiceV := { svc with declared := [("mail", .externalCommand "ping" .str .int .int)] }
#guard last undeclared [.command ⟨0, by decide⟩ (1 : Int) (5 : Int), .command ⟨0, by decide⟩ (1 : Int) (1 : Int),
  .clock 10] == "fault invalidEffect ping [declared]"
-- A request to an external query: an answer that breaks what the query ensures is Invalid, and the request stays
-- pending for another answer.
def rate : EffectV .int := .request
  { name := "rate", input := .str, output := .int, rejection := none, value := "eur",
    holds := fun o => rule "positive" (decide (0 < I o)), onAnswer := fun (o, ()) => [o] }
def asking : ServiceV :=
  { svc with machines := [{ watch with effect := fun _ st _ _ => if I st = 5 then some rate else none }],
             declared := [("fx", .externalQuery "rate" .str .int fun _ => [])] }
def askingUntil : List (Input asking) :=
  [.command ⟨0, by decide⟩ (1 : Int) (5 : Int), .command ⟨0, by decide⟩ (1 : Int) (1 : Int), .clock 10]
#guard last asking (askingUntil ++ [.answer 0 ⟨.int, (-1 : Int)⟩]) == "invalid [positive]"
#guard last asking (askingUntil ++ [.answer 0 ⟨.int, (-1 : Int)⟩, .answer 0 ⟨.int, (3 : Int)⟩]) == "accepted"
-- `spec` finds the owner of each subscribed source by its name and event type: the external that declares `moved`
-- with Int events, not the one whose `moved` carries text.
def specWith (xs : List ExternalV) : SpecV := Prim.spec.den [] rfl (([svc] : List ServiceV), xs, ())
#guard ((specWith [⟨"text", [.source "moved" .str]⟩, ⟨"clock", [.source "moved" .int]⟩]).services.map fun v =>
  v.subscribes.map (·.source)) == [["clock"]]
#guard ((specWith [⟨"text", [.source "moved" .str]⟩]).services.map fun v => v.subscribes.map (·.source)) == [[""]]
#guard ((SpecV.illegal prelude (specWith [⟨"text", [.source "moved" .str]⟩])).filter (·.1 == .unknownSource)).length == 1
-- Every input has one outcome.
#guard (run svc s0 [cmd 1 5, cmd 2 5, .clock 3]).2.length == 3

end Tazuna.Ir.StepExamples
