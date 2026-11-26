# Guarantees

Lean definitions in `lean/Tazuna` give a spec its meaning, and Lean theorems prove what each command's output says about that meaning.
This page is that contract.
It states what each verdict claims, what it assumes, and what you trust.
Each claim names its theorem as `lean/Tazuna/Axioms.lean` lists the roots.
The build fails when a root is missing, when a proof uses `sorry`, or when a declaration rests on an axiom beyond Lean's standard three.

For what one kind of line means, run `gleam run -m tazuna -- explain <kind>`; this page does not repeat it.
[Concepts](concepts.md) explains why the rules are what they are.

## Verdicts are scoped to the bounds

`prove` and `generate` ask the Z3 solver about a fixed number of slots per collection, taken from the service's `bounds`:

- `creates` gives the slots of each table field of the records.
- `items` gives the slots of each bag and of the pending requests.
- A list type gets as many slots as its longest literal in the spec.
- `cascade` limits the internal steps of one input.
- `steps` limits the inputs of a run that `generate` and a response's search unroll.

A verdict speaks only of states and inputs that fit the slots.
`Prove.withinBounds` and `Generate.unreached` list in `bounds` every bound a step of the service can go past.
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
With no such model, the line reads `Prove.proved` or `Prove.withinBounds`.

`proved_sound` (T4): where every input kind's lines about a fault read proved, no step of any run from the initial state on inputs that satisfy `validInputs` faults with it.
`run_within` gives its induction over the run: each step from a state within the slots leaves a state within them, and an answer that fits no slot names no pending request of its type, so it changes nothing.
`fault_sound` (T4): where every input kind's lines about a fault read proved or within the bounds, no step of a run from the initial state on inputs that satisfy `validInputs` faults with it, wherever the state the run reached and the input fit the slots.
Both proofs are by induction, so they also need the initial state's invariants to hold, which the `init` lines check.
`Fault.answerUnmatched` is no target, because an answer that names no request is the outside's mistake.

A step line's `assumes` lists `validInputs` and the invariants the induction took as holding that this run did not prove: the violated ones, the undecided ones, and the ones `--only` left out.

`cti_sound`, for `Prove.violated` with `"from":"validState"`: the state keeps the step invariant and every invariant, and the step Lean computes from it is the one the solver's terms describe.
`step_settled`: `after` is the state the step reaches before its invariant check.

## prove: dead targets

For each of `generate`'s targets, `prove` asks per input kind whether a step from a state of the right shape where every invariant holds shows the target's class, the same question as a T4 step line with that goal in place of a broken rule.
It prints `Prove.unreachable` only where every input kind's question is unsat, and nothing otherwise: a model's state may be one no run reaches.
A target that only a query's answer shows gets no question, since no step question is about a query.
Nor does any target of a service whose initial state breaks an invariant or one of whose input kinds is refused.

- `unshown_sound`: where every bound question reads proved and every input and the initial state fit the slots, no step of any run from the initial state, on inputs that satisfy `validInputs`, that faults nowhere shows the class. The line has no `bounds`.
- `unshown_within`: otherwise, the same for every step within the slots, and the line names the `bounds` as a `Prove.withinBounds` line does.

Both rest on `run_invariants` and `run_supp`: every state such a run reaches has the shape the question assumes, whether or not the invariants were proved.
The line exits 0, like a compiler warning, because a defensive branch may be meant never to run.
`Generate.unreached` still has a job: a target whose question has a model, from a state no run reaches, gets no `Prove.unreachable` line, but `generate` can still find no run of at most `steps` inputs to it.

## prove: order of own steps and timers (T5)

Two kinds of line check that no outcome depends on the order in which the semantics runs own steps and timers ([Concepts](concepts.md#the-spec-writes-every-order)):

- A pair line, `<first> and <second> commute`, asks for a state and two waiting own effects whose two orders end differently, with each effect keeping the ids it made.
- A timer line, `timers of <machine> fire forward`, asks whether the machine's `after` can set a timer before the current time.

`run_lines` (T5): take a run from the initial state whose inputs satisfy `validInputs`, and a cascade that one of its steps starts at a state and an input within the slots.
Where every state the cascade reaches in any order fits the slots, and every step line and pair line reads proved or within the bounds, every order of the cascade ends as the semantics' order does, up to renaming the ids the cascade made, or both orders fault.
Where every timer line reads proved, the same holds for the timers due at one deadline of a clock line.
The proof composes the commutation of one step with another, so a pair whose orders meet again only after later steps reads as not commuting.

A pair line's `widened` names an own kind that a send with no handle or `on_answer` written in place makes.

A violated pair or timer line rests on these theorems:

- `pair_violates`: a pair's counterexample shows that the pair does not commute. Either one order faults or disables the other step and the other order does not, or both orders finish and no renaming of the ids the pair made gives them the same data. Lean searches every such renaming, both counters kept or swapped and each wire id the pair made mapped one to one onto the other order's, so finding none means none exists.
- `timer_violates`: a timer line's counterexample is a context whose `after` sets a timer before the current time.

## prove: responses (T7)

A response states "after each event `trigger` satisfying `after`, an event satisfying `then(trigger, event)` within `within` ms".
A `within 0` response is first asked in one step: whether a step of each input kind, from a state of the right shape where every invariant holds, applies a trigger that no event of the same step answers.

- `Prove.proved`: `response_proved`: where every kind's question and bound question is unsat and every input and the initial state fit the slots, no run from the initial state on inputs that satisfy `validInputs` violates the response, at any depth. Each trigger is answered in its own step. A model says nothing, since a later step at the same time may answer.

Otherwise `prove` searches the runs from the initial state of 1 to `steps` inputs for one that violates the response, and the line reads:

- `Prove.violated`: `response_sound`: the run's inputs satisfy `validInputs`, its clock lines are timely, and it violates the response.
- `Prove.withinBounds`: `response_within` (T7), at each depth up to `steps`: no run of that many inputs within the slots, on which the line's `assumes` hold and at whose events the response's functions fit the slots, violates it.

A response is judged per step, so a `then` event in the same step as its trigger counts.

## generate (T6)

`generate <root> <dir>` aims at each class of out line a service can show: `<command> accepted`, `<command> rejected <Variant>`, `<request> invalid <rule>`, `<query> answered`, `event <Variant>`, and `request <external>.<name>`.
Answers are to request lines, which come from outside, so the targets follow `callers`.
A command or query that lists no `Outside` caller has only `<request> invalid callers`: an outside request must be refused.
`<request> invalid callers` is left out when `callers` lists `Outside` of every value of a caller type whose variants have no fields, since no request line can then be refused for its caller.
`targets_cover`: every class of out line a step can show is aimed at by one of these targets.
For each target, `generate` searches runs from the initial state, one input longer each time, up to `steps` inputs.

- `Generate.reached` writes the trace of the shortest run it found to `<dir>/<service>/<target>.jsonl`. `generate_reaches` (T6): the written trace reads as the spec from the initial state, so `verify` replays it as passed unless it runs out of tries, and the last step of its run shows the target. `generate_sound`: every model the solver gives decodes to inputs that satisfy `validInputs` whose run faults nowhere and reaches the target. `targetFile_inj`: two targets never share a file, so no written trace overwrites another's.
- `Generate.unreached`: `generate_unreached` (T6b): no run of at most `steps` inputs within the slots, on which the line's `assumes` hold, shows the target's class at any step.

## verify

`verify <root> <dir>` replays each `.jsonl` trace in the directory against the spec.
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

| Text in `assumes` | Lines that print it |
| --- | --- |
| `ids the service made are used only after they appeared on an out line` | step lines, pair lines, responses, `Prove.unreachable`, `Generate.unreached` |
| `no step of the run faults` | responses, `Prove.unreachable`, `Generate.unreached` |
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
- Z3. An unsat answer is trusted. A sat answer is not, because Lean decodes the model and recomputes the counterexample or replays the run. The answer cache, keyed by SHA-256 digests of the script and of the solver's version, holds answers you trust in the same way.
- The release. On first run the launcher fetches the engine and z3 from the GitHub release of its own version and refuses any file whose SHA-256 differs from the one the Hex package pins, so you trust the release workflow that built and pinned them. With `TAZUNA_ENGINE` set you trust that engine instead, and the z3 on PATH.
- SMT-LIB. `Term.denote` states the standard's meaning of each term, and you trust that Z3 implements it. Division and remainder by 0 are free in the model, as the standard leaves them. Strings hold code points up to U+2FFFF, the standard's string domain. A Lean string value is a `Tazuna.Str`, which holds no other, and `Smt.Unsat` quantifies over models whose strings stay in that domain, so an unsat answer covers exactly the strings Z3 searched.

## Not guaranteed

- A pair line that reads `Prove.proved` covers every run only where every order of a cascade stays within the slots. `run_within` keeps the states between inputs within them, but no theorem yet keeps the cascade's other orders there.
- `Undecided.upToRenaming` says the two orders end the same once renamed. That rests on Lean's comparison of their terms under the renaming it found, and no theorem yet says such orders are the same as the oracle sees them. The line is undecided, so no verdict rests on it.
- The `bounds` list over-states lists. Every list type of the layout appears with its longest literal, though a list that only literals build cannot grow.
- `Undecided.timeout` depends on the machine. Z3 ran past a 10-minute wall clock before its resource limit stopped it, though the limit takes about 6 seconds on a laptop. Every other answer, `Undecided.unknown` included, comes from Z3's fixed resource limit and seeds, so it is the same on every machine.
- Ids that cannot be guessed, authentication, and anything else outside the spec's values are the implementation's concern.
