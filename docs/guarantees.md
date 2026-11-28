# Guarantees

Lean definitions in `lean/Tazuna` give a spec its meaning, and Lean theorems prove what each command's output says about that meaning.
This page is that contract.
It states what each verdict claims, what it assumes, and what you trust.
Each claim names its theorem as `lean/Tazuna/Axioms.lean` lists the roots.
The build fails when a root is missing, when a proof uses `sorry`, or when a declaration rests on an axiom beyond Lean's standard three.

For what one kind of line means, run `gleam run -m tazuna -- explain <kind>`; this page does not repeat it.
[Concepts](concepts.md) explains why the rules are what they are.

## One question per target

Every target asks whether a run from the initial state reaches it.
A target that a fault breaks (an invariant, an `ensures` rule, `effect <name> accepted`, `cascade bound`) is a bug where a run reaches it.
A behavior target, a class of out line, gives a test input where a run reaches it.
`prove` answers from one step, and `generate` searches runs of at most `steps` inputs:

```
target a fault breaks
├─ the initial state breaks it ........ Prove.violated                      exit 1
├─ no step breaks it .................. Prove.proved, Prove.withinBounds    exit 0
└─ a step breaks it ................... Prove.unproved                      exit 2
   ├─ generate finds a run ............ Generate.violated, trace written    exit 1
   ├─ no run within steps ............. Generate.unsettled                  exit 2
   └─ the solver gives no answer ...... Undecided.*                         exit 2
behavior target
├─ no step shows it ................... Prove.unreachable, Generate.unreachable  exit 0
├─ generate finds a run ............... Generate.reached, trace written     exit 0
├─ no run within steps ................ Generate.unreached                  exit 0
└─ the solver gives no answer ......... Undecided.*                         exit 2
```

`Prove.unproved` is a counterexample to induction: a state where every invariant holds and a step from it that breaks the target, which no run may reach.
Only the initial state, or a run from it that Lean runs and `verify` replays, makes a target violated.
A response's, a pair's and a timer machine's line has no fault to search for, so its `Prove.unproved` line stays open.

## Verdicts are scoped to the bounds

`prove` and `generate` ask the Z3 solver about a fixed number of slots per collection, taken from the service's `bounds`:

- `creates` gives the slots of each table field of the records.
- `others_at_most` gives the slots of every other bag and table: bags anywhere, tables inside values, each machine's table of instances, and the pending requests.
- Every collection type gets at least as many slots as the longest list literal in the spec that writes its items: a list type its own, `Bag(a)` that of `List(a)`, and `Table(k, v)` that of `List(#(k, v))`, as `bag.from_list` and `table.from_list` take them. So every value the spec writes fits, and `bounds` names such a type's bound `longest literal`.
- `cascade` limits the internal steps of one input.
- `steps` limits the inputs of a run that `generate` unrolls.

A verdict speaks only of states and inputs that fit the slots.
`Prove.withinBounds`, `Generate.unreached` and `Generate.unsettled` list in `bounds` every bound a step of the service can go past.
That list is the service's static scope, the same in every run.

## check

`check` loads the IR and evaluates `spec()`.
Every command but `explain` runs `check` first and stops at a finding.

`wireTys_wire`: when `check` finds nothing, every type that crosses the wire holds no function and no fresh-id source.
The other rules have no theorem beyond their definition in `Tazuna.Ir.Illegal`.
`Illegal.callers` reads the sends in the spec's source, so a send whose handle it cannot pin down (a handle passed as a value) can still reach a command or query without `Own`, which is `Fault.invalidEffect` at run time.

## test

`test` runs each scenario in the semantics, from `init` at time 0, and compares its trace with `snapshots/<service>/<scenario>.jsonl` line by line as text.
Before comparing or writing (`test --update`), `test` replays the trace with the same function `verify` runs on a file.
No theorem says that a scenario's trace passes, so a trace that does not pass is a tazuna bug: `test` prints `Internal.engine`.

`TraceFile.read_wires`: reading a written trace back gives its header and lines back.
So with `replay_iff` (see verify), a snapshot that `test` wrote or passed is one `verify` passes.

## prove: invariants, ensures, and the cascade (T4)

`prove` asks about each target of each service: every service and machine invariant, each `ensures` rule, `cascade bound` (no input takes more internal steps than `cascade`), and `effect <name> accepted` (no own effect asks for what its target does not accept).
It prints one `init` line per service invariant, from evaluating the initial state.
For each target it prints one line per input kind: each command, each answer to a pending request, each subscribed event, and the clock.

A step line asks the solver for a state of the right shape where every invariant holds, and an input, whose step breaks the target.
The right shape includes that every id the service made in the state is below its counter, so an id the step makes is new.
`run_supp` proves every state a run reaches on inputs that satisfy `validInputs` has that shape, which is why step lines print it in `assumes`.
The right shape also includes that each machine has an instance for exactly the keys its `instances` gives at the records.
`run_keys` proves every state a run reaches has it with no assumption on the inputs, because check requires that `instances` gives no key at the initial records (`Illegal.initialInstances`).
With no such model, the line reads `Prove.proved` or `Prove.withinBounds`.
With one, it reads `Prove.unproved`, and an `init` line whose initial state breaks the invariant reads `Prove.violated`.

`proved_sound` (T4): where every input kind's lines about a fault read proved, no step of any run from the initial state on inputs that satisfy `validInputs` faults with it.
`run_within` gives its induction over the run: each step from a state within the slots leaves a state within them, and an answer that fits no slot names no pending request of its type, so it changes nothing.
`fault_sound` (T4): where every input kind's lines about a fault read proved or within the bounds, no step of a run from the initial state on inputs that satisfy `validInputs` faults with it, wherever the state the run reached and the input fit the slots.
Both proofs are by induction, so they also need the initial state's invariants to hold, which the `init` lines check.
`Fault.answerUnmatched` is no target, because an answer that names no request is the outside's mistake.

A step line's `assumes` lists `validInputs` and the invariants the induction took as holding that this run did not prove: the unproved ones, the undecided ones, and the ones `--only` left out.

`cti_sound`, for `Prove.unproved`: the state keeps the step invariant and every invariant, and the step Lean computes from it is the one the solver's terms describe.
`step_settled`: `after` is the state the step reaches before its invariant check.

## prove: dead targets

For each of `generate`'s targets, `prove` asks per input kind whether a step from a state of the right shape where every invariant holds shows the target's class, the same question as a T4 step line with that goal in place of a broken rule.
It prints `Prove.unreachable` only where every input kind's question is unsat, and nothing otherwise: a model's state may be one no run reaches.
Before asking, `prove` reads the code, and a kind whose step cannot show the class gets no question (`Step.step_events`).
A step applies only events built by a constructor written in a function it runs: the input's own (`decide`, `wrap`, an `on_answer` of the answer's type) and the cascade's (every machine's `effect`, every reaction, every command the service runs as `Own`).
A request's `on_answer` runs when its answer comes, so its constructors count for that answer, not for the step that sends the request.
So a kind whose functions write no constructor of the target's event cannot show it, and a kind that applies no event and is no clock line sends no request.
A query, and a command that no outside caller may send, applies no event and sends nothing.
This reading holds only where no value a step starts from can hold an event: the records, the callers, the machines' keys and states, the commands' inputs and rejections, the queries' outputs, the subscriptions' events and the values the kept functions captured.
Where one can, every kind is asked.
A target's questions run in the input kinds' order and stop at the first answer that is not unsat, since that answer already rules the line out.
A target that only a query's answer shows gets no question, since no step question is about a query.
Nor does any target of a service whose initial state breaks an invariant or one of whose input kinds is refused.

- `unshown_sound`: where every bound question reads proved and every input and the initial state fit the slots, no step of any run from the initial state, on inputs that satisfy `validInputs`, that faults nowhere shows the class. The line has no `bounds`.
- `unshown_within`: otherwise, the same for every step within the slots, and the line names the `bounds` as a `Prove.withinBounds` line does.

Both rest on `run_invariants` and `run_supp`: every state such a run reaches has the shape the question assumes, whether or not the invariants were proved.
The line exits 0, like a compiler warning, because a defensive branch may be meant never to run.
`generate` asks the same questions from its second length on and prints `Generate.unreachable` for such a target.
A target whose question has a model, from a state no run reaches, gets no `Prove.unreachable` line, and `generate` may still find no run of at most `steps` inputs to it (`Generate.unreached`).

## prove: order of own steps and timers (T5)

Two kinds of line check that no outcome depends on the order in which the semantics runs own steps and timers ([Concepts](concepts.md#the-spec-writes-every-order)):

- A pair line, `<first> and <second> commute`, asks for a state and two waiting own effects whose two orders end differently, with each effect keeping the ids it made.
  Where no input kind's cascade can queue effects of both kinds, the two never wait together, so the line reads as if both questions were unsat and no question is asked.
  An input kind's cascade queues only the own effects whose `on_answer` the events it can apply, and the machine states it can enter, can write.
- A timer line, `timers of <machine> fire forward`, asks whether the state a timer of the machine enters can wait for a timer before the one that fired. A timer is read off the instance's state and the records, so the question has no time in it.

`run_lines` (T5): take a run from the initial state whose inputs satisfy `validInputs`, and a cascade that one of its steps starts at a state and an input within the slots.
Where every state the cascade reaches in any order fits the slots, and every step line and pair line reads proved or within the bounds, every order of the cascade ends as the semantics' order does, up to renaming the ids the cascade made, or both orders fault.
Where every timer line reads proved, the same holds for the timers due at one deadline of a clock line.
The proof composes the commutation of one step with another, so a pair whose orders meet again only after later steps reads as not commuting.

A pair line's `widened` names an own kind that a send with no handle or `on_answer` written in place makes.

A pair or timer line with a counterexample reads `Prove.unproved`, since its state is any state of the right shape, and rests on these theorems:

- `pair_violates`: a pair's counterexample shows that the pair does not commute. Either one order faults or disables the other step and the other order does not, or both orders finish and no renaming of the ids the pair made gives them the same data. Lean searches every such renaming, both counters kept or swapped and each wire id the pair made mapped one to one onto the other order's, so finding none means none exists.
- `timer_violates`: a timer line's counterexample is an instance and records whose timer enters a state that waits for an earlier timer.

## prove: responses (T7)

A response states "after each event `trigger` satisfying `after`, an event satisfying `then(trigger, event)` within `within` ms".
Its `deadline` reads the deadline the records keep for a trigger while it waits for its answer, and none once it waits no more.
`prove` proves a response by induction over steps, as Lamport's "Real Time is Really Simple" (2005, sec 3.3) proves a bounded response from an invariant on a deadline variable.

A response is a target, with one line per input kind.
The line asks the solver for a state of the right shape where every invariant holds, an input, and a trigger value, whose step does one of three things:

1. The step applies a trigger, no event of the same step answers it, and after the step its deadline is missing or later than the step's time plus `within`.
2. The trigger had the deadline `d` before the step, no event of the step answers it, and after the step its deadline is missing or later than `d`. This part is asked only where every machine's `instances` fits the slots at the records, so the instance shape holds in full.
3. The step is a timely clock line to a time past the trigger's deadline `d`. This part also needs `instances` to fit.

A response is judged per step, so a `then` event in the same step as its trigger counts.

- `Prove.proved`: `response_holds` (T7): where every kind's line and bound question is unsat, and every input and the initial state fit the slots, no run from the initial state on inputs that satisfy `validInputs`, with timely clock lines, violates the response, at any length.
- `Prove.withinBounds`: `response_scoped` (T7): where every kind's line is unsat, the same of every run whose steps stay within the slots.
- `Prove.unproved`: the step breaks one of the three parts, recomputed in Lean from the model's state, input and trigger. Like a step line's counterexample, it comes from a state of the right shape, which no run may reach; another invariant can rule it out (a machine invariant may read `now`). `generate` searches no run for it: a reachable state that breaks a part violates the response only once a later step passes the trigger's time plus `within` unanswered.

`not_violated` (`Semantics/Response.lean`) turns the three facts into the run's: after the trigger's step its deadline is at most its time plus `within`; each later step that does not answer keeps the deadline no later; and time moves only on clock lines, which pass no waiting deadline.
A step within the slots ends with every machine's `instances` fitting at the records it leaves (the bound question asks it), so parts 2 and 3 hold at every step after the trigger's.

The proof reads only the records, so whatever answers a trigger must change the records the deadline reads. An event that `apply` folds into nothing cannot close a trigger: write down in the records that it happened.

## generate (T6)

`generate <root> <dir>` aims at each class of out line a service can show: `<command> accepted`, `<command> rejected <Variant>`, `<request> invalid <rule>`, `<query> answered`, `event <Variant>`, and `request <external>.<name>`.
Answers are to request lines, which come from outside, so the targets follow `callers`.
A command or query that lists no `Outside` caller has only `<request> invalid callers`: an outside request must be refused.
`<request> invalid callers` is left out when `callers` lists `Outside` of every value of a caller type whose variants have no fields, since no request line can then be refused for its caller.
A command gets `<command> rejected <Variant>` only for the constructors its `decide` may return.
Where `decide` writes every rejection in place as a constructor, in `require`, `lookup` or `Error(..)`, through `let` and `case`, those are the constructors it names (`Expr.rejects_sound`); anywhere else, such as a rejection held in a variable or returned by a helper function, every constructor of the rejection type stays a target.
`targets_cover`: every class of out line a step can show is aimed at by one of these targets.
For each target, `generate` searches runs from the initial state, one input longer each time, up to `steps` inputs.
It splits each length into cubes that fix the input kinds of the last steps: one cube per kind of the last step, and a cube the solver leaves undecided splits again on the step before (cube and conquer).
Before it splits, such a cube is asked once more with four times the resource limit, and only an unsat answer is read, so the split is skipped where the cube has no model and the run found is the one the split finds.
Cubes are asked a fixed number at a time, and the first in order with a model wins, so the questions and the trace do not depend on `--jobs`.
A cube needs no question where the code rules out that its last step's kinds show the target, or, from the second length on, where `prove`'s dead-target question of each kind of its last step is unsat.

- `Generate.reached` writes the trace of the shortest run it found to `<dir>/<service>/<target>.jsonl`. `generate_reaches` (T6): the written trace reads as the spec from the initial state, so `verify` replays it as passed unless it runs out of tries, and the last step of its run shows the target. `generate_sound`: every model the solver gives decodes to inputs that satisfy `validInputs` whose run faults nowhere and reaches the target. `targetFile_inj`: two targets never share a file, so no written trace overwrites another's.
- `Generate.unreached`: `noModel_cubes` (T6b): no run of at most `steps` inputs within the slots, on which the line's `assumes` hold, shows the target's class at any step. Every input's kind is one a split lists, so cubes with no model at a length leave no run of that length.
- `Generate.unreachable`: every input kind's dead-target question is unsat, as for `Prove.unreachable` (`unshown_within`), so no run of any length shows the class.

For each target a fault breaks whose `Prove.unproved` lines some input kind has, `generate` searches runs the same way, for a run whose steps fault nowhere until the last, which faults by a fault the target covers.
The last step of every cube takes only the input kinds whose step question, whether a step from a state where every invariant holds breaks the target, is not unsat.
One question per kind first asks whether its step breaks any target a fault breaks, so most kinds need no question per target.
A target that every kind's question rules out is settled by `prove` and gets no line.

- `Generate.violated` writes the run's trace, up to the last step's `in` line, to `<dir>/<service>/violated/<target>.jsonl`. `generate_breaks`: the run, in Lean, faults nowhere before its last step and faults there by a fault the target covers, and `verify` replays the trace to such a fault at its last line.
- `Generate.unsettled`: `noModel_breaks`: no run of at most `steps` inputs within the slots, on valid inputs, whose steps before the last fault nowhere, faults at its last step by a fault the target covers.

## verify

`verify <root> <dir>` replays each `.jsonl` trace in the directory and its subdirectories against the spec, so `verify <root> inputs` reads what `generate <root> inputs` wrote.
Each `in` line runs as the spec's input.
The `out` lines up to the next `in` line form its window, which must hold the spec's `out` lines in some order.
The implementation names its ids and request ids its own way.
One binding, one to one, names the spec's ids by the trace's names, each from its first appearance on an `out` line.
An id that an `in` line names before any `out` line showed it is an id from outside the service.

`replay_iff`: unless `verify` runs out of tries, it prints `Verify.passed` exactly when some binding reads every window as the spec's.
After 100,000 tries it prints `Undecided.limit`.

## Assumptions

Three assumptions appear in `assumes`, in these words.
`Assumption.text` in `Semantics/Valid.lean` defines each text beside its meaning, so the two cannot part.
`Generate.unsettled` also prints `no step before the last faults`, since its run ends in a fault.

| Text in `assumes` | Lines that print it |
| --- | --- |
| `ids the service made are used only after they appeared on an out line` | step lines, pair lines, responses, `Prove.unreachable`, `Generate.unreached`, `Generate.unreachable`, `Generate.unsettled` |
| `no step of the run faults` | `Prove.unreachable`, `Generate.unreached`, `Generate.unreachable` |
| `no clock line moves time past a timer that waits` | responses |

The first leaves ids from outside the service unrestricted.

The model itself assumes more, and no line prints it:

- An implementation finishes an input before the next `in` line, so all of an input's `out` lines come before it. Inside a step, the cascade runs to completion.
- Time moves and timers fire only on clock lines (`{"in":"clock"}`). A trace that wants a timer to fire writes a clock line.
- State is durable. The inputs are requests, answers, events, and clock lines, with no restart. To specify a restart that loses state, write the loss as an event from a declared external.

## Trusted base

You trust these programs and documents.
Everything between them is proved or checked.

- Gleam. `gleam build` type-checks the spec before the converter reads it.
- glance. The converter parses each module with it. On every conversion, the converter prints the IR back as Gleam and compares what glance reads from that text with what it read from the source.
- The Lean kernel checks every proof, and the Lean compiler builds the engine. Where compiled code uses a faster form, a root proves the two equal: `SExp.print_eq_printFast`, `Term.denote_eq_denoteFast`, `Term.beq_eq_beqFast`, and `Defs.add_eq_addFast`.
- Lean's JSON printer and parser stand between wire values and a trace's text.
- Z3. An unsat answer is trusted. A sat answer is not, because Lean decodes the model and recomputes the counterexample or replays the run. The answer cache, keyed by SHA-256 digests of the script and of the solver's version, holds answers you trust in the same way. It also keeps an unknown answer, which the resource limit and seeds written in the script decide, but never a timeout. prove first looks a question up by a key of what builds its script, as ccache's direct mode does: the SHA-256 of the engine executable, Z3's version and the options the engine writes, the SHA-256 of the IR, and which question it is. That key never reads the script, so it trusts the engine to build the same script from the same inputs, as it is deterministic. Another engine, Z3 or spec misses it, and the script's own key still finds every unchanged answer.
  Z3 reads each script with the name of every id from outside as an Int code, since a step only compares such names, and the script as it is where a name meets any other operation. `code_model` proves that a model of the script gives a model of what Z3 reads, so an unsat answer is the script's (`Unsat.noModel`). A sat answer's codes read back as fixed names in the same order (`nameOf_lt`).
  Where that script holds strings, Z3 first reads an abstract variant of it: every string is an Int code, each literal a variable kept in the literals' order, `str.<` is `<`, and `str.++` and `str.len` are functions Z3 may choose freely. `abs_model` proves that a model of the script gives a model of the variant, so an unsat answer to the variant is the script's too. A sat answer to the variant may come from codes that no strings realize, so it is never read. Z3 is asked the script again with the variant's model fixed, first with each code as a string in the codes' order, then with only the values that are not strings, and Lean reads that answer as any other. Where neither finds a model, the script itself answers.
- The release. On first run the launcher fetches the engine and z3 from the GitHub release of its own version and refuses any file whose SHA-256 differs from the one the Hex package pins, so you trust the release workflow that built and pinned them. With `TAZUNA_ENGINE` set you trust that engine instead, and the z3 on PATH.
- SMT-LIB. `Term.denote` states the standard's meaning of each term, and you trust that Z3 implements it. Division and remainder by 0 are free in the model, as the standard leaves them, and so is a declared function, any function from Ints to an Int. Strings hold code points up to U+2FFFF, the standard's string domain. A Lean string value is a `Tazuna.Str`, which holds no other, and `Smt.Unsat` quantifies over models whose strings stay in that domain, so an unsat answer covers every string a value can hold.
  An SMT-LIB model holds only values of their sorts, including a selector applied to a value of another constructor, which the standard leaves open, and the items of a collection's free slots. `Smt.Unsat` quantifies only over models that do so (`WellSorted`), and Z3 answers only scripts that are well sorted and whose datatypes hold values. So every model `Smt.Unsat` rules out is one Z3 searched, and the claim says no more than the answer.

## Not guaranteed

- A pair line that reads `Prove.proved` covers every run only where every order of a cascade stays within the slots. `run_within` keeps the states between inputs within them, but no theorem yet keeps the cascade's other orders there.
- `Undecided.upToRenaming` says the two orders end the same once renamed. That rests on Lean's comparison of their terms under the renaming it found, and no theorem yet says such orders are the same as the oracle sees them. The line is undecided, so no verdict rests on it.
- The `bounds` list over-states lists. Every list type of the layout appears with its longest literal, though a list that only literals build cannot grow.
- `Undecided.timeout` depends on the machine. Z3 ran past a 10-minute wall clock before its resource limit stopped it, though the limit takes about 6 seconds on a laptop. Every other answer, `Undecided.unknown` included, comes from Z3's fixed resource limit and seeds, so it is the same on every machine.
- Ids that cannot be guessed, authentication, and anything else outside the spec's values are the implementation's concern.
