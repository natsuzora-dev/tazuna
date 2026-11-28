import Tazuna.Semantics.Builtin
import Tazuna.Semantics.Step

/-! One example per step rule, on a small service: the records are a running total, a command adds a positive amount
below 100, the total stays under 50, and a machine that the total's moves bring to state 1 waits for its timer at 10 ms,
then pings an external whose answer adds 1. -/

namespace Tazuna.Ir.StepExamples

open Step

private def I (x : Int) : Int := x
private def rule (n : String) (b : Bool) (h : inDomain n = true := by decide) : Ty.rules.den0 := [(⟨n, h⟩, Ty.ofBool b, ())]

/-- Named rules with one rule. -/
private def ruleE {Γ : List Ty} (n : String) (b : Expr [] Γ Ty.bool) (h : inDomain n = true := by decide) :
    Expr [] Γ Ty.rules :=
  .list (.cons (.tuple (.cons (.str ⟨n, h⟩) (.cons b .nil))) .nil)
private def recordsE {Γ : List Ty} (x : Expr [] Γ (Ty.ctx .int .int .int)) : Expr [] Γ .int :=
  .field (ft := .int) "records" 0 (by simp) x
private def inputE {Γ : List Ty} (x : Expr [] Γ (Ty.ctx .int .int .int)) : Expr [] Γ .int :=
  .field (ft := .int) "input" 1 (by simp) x
/-- The records `apply` sees. -/
private def applyRecordsE {Γ : List Ty} {r : Ty} (x : Expr [] Γ (Ty.applyCtx r)) : Expr [] Γ r :=
  .field (ft := r) "records" 0 (by simp) x
private def queryRecordsE {Γ : List Ty} (x : Expr [] Γ (Ty.queryCtx .int .int .int)) : Expr [] Γ .int :=
  .field (ft := .int) "records" 0 (by simp) x

private def iteE {Γ : List Ty} {r : Ty} (c : Expr [] Γ Ty.bool) (a b : Expr [] Γ r) : Expr [] Γ r :=
  .case c (.cons (.ctor (vs := [[], []]) ⟨0, by decide⟩ .nil) a (.cons (.ctor (vs := [[], []]) ⟨1, by decide⟩ .nil) b .nil))
    ⟨4, rfl⟩
/-- A field of the machine context `MachineCtx(key, state, records, now)`. -/
private def mctxE {Γ : List Ty} {k st r : Ty} (label : String) (n : Fin 4) (x : Expr [] Γ (Ty.machineCtx k st r)) :
    Expr [] Γ ([k, st, r, .point .ms].get n) :=
  .field label n.val (by intro fs h; simp at h; subst h; simp) x
/-- A field of the timer context `TimerCtx(key, state, records)`. -/
private def tctxE {Γ : List Ty} {k st r : Ty} (label : String) (n : Fin 3) (x : Expr [] Γ (Ty.timerCtx k st r)) :
    Expr [] Γ ([k, st, r].get n) :=
  .field label n.val (by intro fs h; simp at h; subst h; simp) x
private def enterE {Γ : List Ty} {st : Ty} (x : Expr [] Γ st) : Expr [] Γ (Ty.next st) :=
  .ctor (vs := [[], [st]]) ⟨1, by simp⟩ (.cons x .nil)
private def noTimerE {Γ : List Ty} {st : Ty} : Expr [] Γ (Ty.option (Ty.timer st)) :=
  .ctor (vs := [[Ty.timer st], []]) ⟨1, by simp⟩ .nil
private def timerE {Γ : List Ty} {st : Ty} (d : Expr [] Γ (.point .ms)) (x : Expr [] Γ st) :
    Expr [] Γ (Ty.option (Ty.timer st)) :=
  .ctor (vs := [[Ty.timer st], []]) ⟨0, by simp⟩ (.cons (.ctor (vs := [[.point .ms, st]]) ⟨0, by simp⟩
    (.cons d (.cons x .nil))) .nil)

private def someE {Γ : List Ty} {t : Ty} (x : Expr [] Γ t) : Expr [] Γ (Ty.option t) :=
  .ctor (vs := [[t], []]) ⟨0, by simp⟩ (.cons x .nil)
private def noneE {Γ : List Ty} {t : Ty} : Expr [] Γ (Ty.option t) := .ctor (vs := [[t], []]) ⟨1, by simp⟩ .nil
/-- The `n`th kept function of the global `examples`, capturing nothing. -/
private def keptE {Γ : List Ty} {t : Ty} (n : Nat) (body : Expr [] [] t) (ht : t.isData = true := by rfl) :
    Expr [] Γ (.dsl .closure [t]) :=
  .close ⟨"examples", n⟩ .nil rfl ht body

/-- `request_command(external_command("ping"), "hi", fn(answer) { case answer { Ok(_) -> [1]  Error(_) -> [] } })`. -/
private def pingE {Γ : List Ty} : Expr [] Γ (.dsl .effect [.int]) :=
  .call (.prim .requestCommand [.int, .str, .int, .str] rfl)
    (.cons (.call (.prim .externalCommand [.str, .int, .str] rfl) (.cons (.str (str! "ping")) .nil))
      (.cons (.str (str! "hi"))
        (.cons (keptE 1 (.lam (.case (.var .here)
          (.cons (.ctor (vs := [[.int], [.str]]) ⟨0, by decide⟩ (.cons .wild .nil)) (.list (.cons (.int 1) .nil))
            (.cons (.ctor (vs := [[.int], [.str]]) ⟨1, by decide⟩ (.cons .wild .nil)) (.list .nil) .nil)) ⟨4, rfl⟩)))
          .nil)))

/-- The state of `watch`: a count, and the deadline its last entry set, 10 ms after the event's time; none before
the first entry, since no spec can write an instant. -/
private abbrev watchT : Ty := .tuple [.int, Ty.option (.point .ms)]
private def countE {Γ : List Ty} (x : Expr [] Γ watchT) : Expr [] Γ .int := .index x ⟨0, by decide⟩
private def dueE {Γ : List Ty} (x : Expr [] Γ watchT) : Expr [] Γ (Ty.option (.point .ms)) := .index x ⟨1, by decide⟩

def watch : MachineV .int .int :=
  { name := "watch", key := .int, state := watchT,
    instances := .closed (.lam (.call (.prim .bagFromList [.int] rfl)
      (.cons (iteE (.bin .lt (.int 0) (.var .here)) (.list (.cons (.int 0) .nil)) (.list .nil)) .nil))),
    initial := ((0 : Int), .inr (.inl ()), ()),
    on := .closed (.lam (enterE (.tuple (.cons (.bin .add (countE (mctxE "state" 1 (.var .here))) (.int 1))
      (.cons (someE (.call (.prim .instantAdd [] rfl) (.cons (mctxE "now" 3 (.var .here)) (.cons (.int 10) .nil))))
        .nil))))),
    timer := .closed (.lam (iteE (.bin (.eq rfl) (countE (tctxE "state" 1 (.var .here))) (.int 1))
      (.case (dueE (tctxE "state" 1 (.var .here)))
        (.cons (.ctor (vs := [[.point .ms], []]) ⟨0, by decide⟩ (.cons .bind .nil))
          (timerE (.var .here) (.tuple (.cons (.int 5) (.cons (someE (.var .here)) .nil))))
          (.cons (.ctor (vs := [[.point .ms], []]) ⟨1, by decide⟩ .nil) noTimerE .nil)) ⟨4, rfl⟩) noTimerE)),
    effect := .closed (.lam (iteE (.bin (.eq rfl) (countE (mctxE "state" 1 (.var .here))) (.int 5)) (someE pingE) noneE)),
    invariants := .closed (.lam (.list .nil)) }

private def addAccepts : Expr [] [] (Ty.fn [.int] Ty.rules) := .lam (ruleE "small" (.bin .lt (.var .here) (.int 100)))
private def addDecide : Expr [] [] (Ty.fn [Ty.ctx .int .int .int] (Ty.result (.list .int) .str)) :=
  .lam (.call (.prim .require [.list .int, .str] rfl)
    (.cons (.bin .lt (.int 0) (inputE (.var .here))) (.cons (.str (str! "positive"))
      (.cons (.lam (.ctor (i := 2) (args := [.list .int, .str]) ⟨0, by decide⟩
        (.cons (.list (.cons (inputE (.var .here)) .nil)) .nil))) .nil))))
private def addEnsures : Expr [] [] (Ty.fn [Ty.ctx .int .int .int, .int] Ty.rules) :=
  .lam (ruleE "grows" (.bin .le (recordsE (.var .here)) (.var (.there .here))))

def add : CommandV .int .int .int :=
  { name := "add", input := .int, rejection := .str, callers := [Step.outside (c := .int) (1 : Int), Step.own],
    accepts := .closed addAccepts, decide := .closed addDecide, ensures := .closed addEnsures }

/-- The command `add` as a spec writes it. -/
private def addE {Γ : List Ty} : Expr [] Γ (.dsl .command [.int, .int, .int, .int, .str]) :=
  .call (.prim .command [.int, .int, .int, .int, .str] rfl)
    (.cons (.str (str! "add")) (.cons (.list (.cons (.ctor (i := 12) (args := [.int]) ⟨0, by decide⟩ (.cons (.int 1) .nil))
        (.cons (.ctor (i := 12) (args := [.int]) ⟨1, by decide⟩ .nil) .nil)))
      (.cons (keptE 2 addAccepts) (.cons (keptE 3 addDecide) (.cons (keptE 4 addEnsures) .nil)))))

def total : QueryV .int .int :=
  { name := "total", input := .int, output := .int, callers := [Step.outside (c := .int) (1 : Int)], accepts := .closed (.lam (.list .nil)),
    resolve := .closed (.lam (queryRecordsE (.var .here))) }

def svc : ServiceV :=
  { name := "sum", records := .int, event := .int, caller := .int, init := (0 : Int),
    apply := .closed (.lam (.bin .add (applyRecordsE (.var .here)) (.var (.there .here)))),
    subscribes := [{ source := "peer", name := "moved", event := .int, wrap := .closed (.lam (.var .here)) }],
    declares := [.command .int .int .int add, .query .int .int total],
    commands := [add], queries := [total], sources := [], machines := [watch], reactions := [], scenarios := [],
    invariants := .closed (.lam (ruleE "under 50" (.bin .lt (.var .here) (.int 50)))), responses := [],
    cascade := 2,
    declared := [("mail", .externalCommand "ping" .str .int .str)] }

def s0 : State svc := State.init svc
def cmd (caller amount : Int) : Input svc := .command ⟨0, by decide⟩ caller amount
def summary (s : State svc) (i : Input svc) : String := (step prelude svc s i).outcome.summary
def after (s : State svc) (is : List (Input svc)) : State svc := (run prelude svc s is).1

-- A command from a caller outside `callers`, or with input breaking `accepts`, is Invalid without deciding.
#guard summary s0 (cmd 2 5) == "invalid [callers]"
#guard summary s0 (cmd 1 500) == "invalid [small]"
-- `decide` rejects, or accepts with its events.
#guard summary s0 (cmd 1 0) == "rejected"
#guard summary s0 (cmd 1 5) == "accepted"
-- An invariant broken after the step is a fault, and the state stays as it was.
#guard summary s0 (cmd 1 60) == "fault invariant under 50"
#guard I (step prelude svc s0 (cmd 1 60)).state.records == 0
-- A query answers from the records.
#guard summary (after s0 [cmd 1 5]) (.query ⟨0, by decide⟩ (1 : Int) (0 : Int)) == "answered"
-- A peer event arrives as one of the service's events.
#guard I (after s0 [.event ⟨0, by decide⟩ (7 : Int)]).records == 7
-- The first event starts the machine's instance; the next enters state 1, which waits for the timer at 10 ms.
#guard let s := after s0 [cmd 1 5]; s.machines.toSigma.map (·.2.map fun i => (timerOf s.records i).isSome) == [[false]]
#guard let s := after s0 [cmd 1 5, cmd 1 1]
  s.machines.toSigma.map (·.2.map fun i => (timerOf s.records i).map (·.1)) == [[some 10]]
-- A clock line before the deadline fires nothing; at it, the instance enters 5, whose effect sends a request.
#guard (step prelude svc (after s0 [cmd 1 5, cmd 1 1]) (.clock 9)).out.length == 0
#guard (step prelude svc (after s0 [cmd 1 5, cmd 1 1]) (.clock 10)).out.map (·.name) == ["ping"]
-- Time does not move back.
#guard summary (after s0 [.clock 5]) (.clock 4) == "invalid [time moves forward]"
-- The answer to the pending request becomes events; an answer to no pending request is a fault.
#guard summary (after s0 [cmd 1 5, cmd 1 1, .clock 10]) (.answer 0 ⟨Ty.result .int .str, .inl ((0 : Int), ())⟩) ==
  "accepted"
#guard summary s0 (.answer 0 ⟨Ty.result .int .str, .inl ((0 : Int), ())⟩) == "fault answerUnmatched"
-- An answer of the wrong type matches no request.
#guard summary (after s0 [cmd 1 5, cmd 1 1, .clock 10]) (.answer 0 ⟨.int, (0 : Int)⟩) == "fault answerUnmatched"
-- A reaction sends the service's own `add` for some events: 7 adds 2, 1 adds 1 again and again, 3 adds 500.
/-- `send_command(add, n, fn(_) { [] })`. -/
private def sendE {Γ : List Ty} (n : Int) : Expr [] Γ (.dsl .effect [.int]) :=
  .call (.prim .sendCommand [.int, .int, .int, .int, .str] rfl)
    (.cons addE (.cons (.int n) (.cons (keptE 5 (.lam (.list .nil))) .nil)))
def again : ReactionV .int .int :=
  { name := "again", react := .closed (.lam
      (let e : Expr [] ([Ty.reactionCtx .int, .int] ++ []) .int := .var (.there .here)
       let is (k : Int) : Expr [] ([Ty.reactionCtx .int, .int] ++ []) Ty.bool := .bin (.eq rfl) e (.int k)
       iteE (is 7) (.list (.cons (sendE 2) .nil)) (iteE (is 1) (.list (.cons (sendE 1) .nil))
         (iteE (is 3) (.list (.cons (sendE 500) .nil)) (.list .nil))))) }
def loop : ServiceV := { svc with reactions := [again] }
def ev (x : Int) : Input loop := .event ⟨0, by decide⟩ x
-- The own command runs within the step: both events are applied.
#guard I (step prelude loop (State.init loop) (ev 7)).state.records == 9
#guard ((step prelude loop (State.init loop) (ev 7)).events.map I) == [7, 2]
-- An own command with input it does not accept is a fault, not Invalid.
#guard (step prelude loop (State.init loop) (ev 3)).outcome.summary == "fault invalidEffect add [small]"
-- More internal steps than the cascade bound is a fault.
#guard (step prelude loop (State.init loop) (ev 1)).outcome.summary == "fault cascadeLimit"
-- Two services that list the same command and query break the owner rule, once for each.
#guard ((SpecV.illegal prelude ⟨[svc, { svc with name := "other" }], []⟩ [] [] fun _ => []) |>.filter (·.1 == .owner)).length == 2
-- So does a service that declares an external's command.
#guard ((SpecV.illegal prelude ⟨[{ svc with declares := [.externalCommand "ping" .str .int .str] }], []⟩ [] [] fun _ => []) |>.filter
  (·.1 == .owner)).length == 1
-- A test helper: a run with no step prints empty.
set_option linter.tazuna.silentDefault false in
/-- The outcome of the last of the inputs, run from the initial state. -/
def last (v : ServiceV) (is : List (Input v)) : String :=
  (((run prelude v (State.init v) is).2.getLast?).map (·.outcome.summary)).getD ""
-- The handle `pingE` makes: check compares it with what each service's `declared` lists, which the spec built from
-- the externals' declarations.
#guard (pingE (Γ := [])).handles.map (fun h => (h.kind, h.name)) == [("external command", some "ping")]
#guard ((SpecV.illegal prelude ⟨[svc], [⟨"mail", [.externalCommand "ping" .str .int .str]⟩]⟩ (pingE (Γ := [])).handles [] fun _ => []) |>.filter
  (·.1 == .unknownHandle)).isEmpty
#guard ((SpecV.illegal prelude ⟨[{ svc with declared := [("mail", .externalCommand "ping" .str .int .int)] }],
    [⟨"mail", [.externalCommand "ping" .str .int .int]⟩]⟩ (pingE (Γ := [])).handles [] fun _ => []) |>.filter
  (·.1 == .unknownHandle)).length == 1
-- A service sends only the commands and queries it declares, by the name and types its own effects carry.
#guard ((SpecV.illegal prelude ⟨[svc], []⟩ [] [] fun _ => [⟨"command", some "add", [.int, .int, .int, .int, .str]⟩]) |>.filter
  (·.1 == .unknownHandle)).isEmpty
#guard ((SpecV.illegal prelude ⟨[svc], []⟩ [] [] fun _ => [⟨"command", some "other", [.int, .int, .int, .int, .int]⟩]) |>.filter
  (·.1 == .unknownHandle)).length == 1
-- A handle built-in passed as a value has no name check can read, so it is Illegal.handleName too.
#guard ((SpecV.illegal prelude ⟨[svc], [⟨"mail", [.externalCommand "ping" .str .int .str]⟩]⟩
  (Expr.prim (G := []) (Γ := []) .externalCommand [.str, .int, .str] rfl).handles [] fun _ => []) |>.filter
  (·.1 == .handleName)).length == 1
-- A handle whose name is no string literal is Illegal.handleName, own ones included; an own handle with a literal name
-- needs no external.
#guard ((SpecV.illegal prelude ⟨[svc], []⟩ [⟨"command", none, [.int]⟩, ⟨"external query", none, [.int]⟩] [] fun _ => []) |>.filter
  (·.1 == .handleName)).length == 2
#guard ((SpecV.illegal prelude ⟨[svc], []⟩ [⟨"command", some "add", [.int]⟩, ⟨"query", some "get", [.int]⟩] [] fun _ => []) |>.filter
  fun f => f.1 == .handleName || f.1 == .unknownHandle).isEmpty
-- Check reports a handle no external declares as Illegal.unknownHandle, so no checked spec reaches this fault: a
-- request to a command no external declares.
def undeclared : ServiceV := { svc with declared := [("mail", .externalCommand "ping" .str .int .int)] }
#guard last undeclared [.command ⟨0, by decide⟩ (1 : Int) (5 : Int), .command ⟨0, by decide⟩ (1 : Int) (1 : Int),
  .clock 10] == "fault invalidEffect ping [declared]"
-- A request to an external query: an answer that breaks what the query ensures is Invalid, and the request stays
-- pending for another answer.
/-- `request_query(external_query("rate", ensures), "eur", fn(rate) { [rate] })`. -/
private def rateE {Γ : List Ty} : Expr [] Γ (.dsl .effect [.int]) :=
  .call (.prim .requestQuery [.int, .str, .int] rfl)
    (.cons (.call (.prim .externalQuery [.str, .int] rfl)
        (.cons (.str (str! "rate")) (.cons (keptE 6 (.lam (ruleE "positive" (.bin .lt (.int 0) (.var (.there .here)))))) .nil)))
      (.cons (.str (str! "eur")) (.cons (keptE 7 (.lam (.list (.cons (.var .here) .nil)))) .nil)))
def asking : ServiceV :=
  { svc with machines := [{ watch with effect := .closed (.lam
      (iteE (.bin (.eq rfl) (countE (mctxE "state" 1 (.var .here))) (.int 5)) (someE rateE) noneE)) }],
             declared := [("fx", .externalQuery "rate" .str .int (.closed (.lam (.list .nil))))] }
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
#guard ((SpecV.illegal prelude (specWith [⟨"text", [.source "moved" .str]⟩]) [] [] fun _ => []) |>.filter (·.1 == .unknownSource)).length == 1
-- Every input has one outcome.
#guard (run prelude svc s0 [cmd 1 5, cmd 2 5, .clock 3]).2.length == 3

-- Instances react and start in key order, never in the order a bag stores its keys or the instances started: one
-- instance per key of a bag of Int, asking `ping` with its key as it enters a state, and entering state 1 on every
-- event.
/-- `request_query(external_query("ping", fn(_, _) { [] }), key, fn(_) { [] })`. -/
private def askKeyE {Γ : List Ty} (key : Expr [] Γ .int) : Expr [] Γ (.dsl .effect [.int]) :=
  .call (.prim .requestQuery [.int, .int, .int] rfl)
    (.cons (.call (.prim .externalQuery [.int, .int] rfl) (.cons (.str (str! "ping")) (.cons (keptE 8 (.lam (.list .nil))) .nil)))
      (.cons key (.cons (keptE 9 (.lam (.list .nil))) .nil)))
def perKey : MachineV (.bag .int) .int :=
  { name := "perKey", key := .int, state := .int, instances := .closed (.lam (.var .here)), initial := (0 : Int),
    on := .closed (.lam (enterE (.int 1))), timer := .closed (.lam noTimerE),
    effect := .closed (.lam (someE (askKeyE (mctxE "key" 0 (.var .here))))),
    invariants := .closed (.lam (.list .nil)) }
def keyed : ServiceV :=
  { name := "keyed", records := .bag .int, event := .int, caller := .int, init := ([] : List Int),
    apply := .closed (.lam (applyRecordsE (.var .here))),
    subscribes := [{ source := "p", name := "e", event := .int, wrap := .closed (.lam (.var .here)) }],
    declares := [], commands := [], queries := [], sources := [], machines := [perKey], reactions := [],
    scenarios := [], invariants := .closed (.lam (.list .nil)), responses := [],
    cascade := 2,
    declared := [("x", .externalQuery "ping" .int .int (.closed (.lam (.list .nil))))] }
def asked (r : Result keyed) : List (Nat × Int) := r.out.map fun o => (o.id, match o.input with | ⟨.int, x⟩ => x | _ => 0)
def tick (s : State keyed) (keys : List Int) : Result keyed :=
  step prelude keyed { s with records := keys } (.event ⟨0, by decide⟩ (0 : Int))
#guard asked (tick (State.init keyed) [3, 1, 2]) == [(0, 1), (1, 2), (2, 3)]
#guard asked (tick (State.init keyed) [2, 1, 3]) == asked (tick (State.init keyed) [3, 1, 2])
-- The instance of 3 started first, yet the new instance of 1 asks first.
#guard asked (tick (tick (State.init keyed) [3]).state [1, 3]) == [(1, 1), (2, 3)]

end Tazuna.Ir.StepExamples
