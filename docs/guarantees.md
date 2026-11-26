# Guarantees

Lean definitions in `lean/Tazuna` give a spec its meaning, and Lean theorems prove what each command's output says about that meaning.
This page is that contract: what each verdict claims, what it assumes, and what you trust.
Each claim names its theorem as `lean/Tazuna/Axioms.lean` lists the roots.
The build fails when a root is missing, when a proof uses `sorry`, or when a declaration rests on an axiom beyond Lean's standard three.

For one kind of line, run `gleam run -m tazuna -- explain <kind>`.
It prints what the line means, the fields it carries, its exit code, and `backedBy`, the roots it rests on.
This page does not repeat that table.
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
That list is the service's static scope, the same in every run: each table, bag, and list type of its layout, and its pending requests when it sends any.

## check

`check` loads the IR and evaluates `spec()`.
It prints one `Illegal.*` line per broken structure rule, and the launcher prints one `Restricted.*` line per Gleam construct outside the spec subset before Lean sees the spec.
A spec with no finding prints nothing and exits 0.
Every command but `explain` runs `check` first and stops at a finding.

`wireTys_wire`: when `check` finds nothing, every type that crosses the wire holds no function and no fresh-id source.
The other rules have no theorem beyond their definition in `Tazuna.Ir.Illegal`.

## test

`test` runs each scenario in the semantics, from `init` at time 0, and compares its trace with `snapshots/<service>/<scenario>.jsonl` line by line as text.
`Test.passed` means every line is equal.
`test --update` writes the snapshot instead.

`TraceFile.read_wires`: reading a written trace back gives its header and lines back.

## prove: invariants, ensures, and the cascade (T4)

`prove` asks about each target of each service: every service and machine invariant, each `ensures` rule, `cascade bound` (no input takes more internal steps than `cascade`), and `effect <name> accepted` (no own effect asks for what its target does not accept).
It prints one `init` line per service invariant, from evaluating the initial state.
For each target it prints one line per input kind: each command, each answer to a pending request, each subscribed event, and the clock.

A step line asks the solver for a state of the right shape where every invariant holds, and an input, whose step breaks the target.
With no such model, the line reads one of two verdicts:

- `Prove.proved` when the kind's bound question has no model either: no step of the kind that starts within the slots leaves them.
- `Prove.withinBounds` when a step of the kind can leave the slots.

`fault_sound` (T4): where every input kind's lines about a fault read one of these, no step of a run from the initial state faults with it, wherever the state the run reached and the input fit the slots.
The proof is by induction, so it also needs the initial state's invariants to hold, which the `init` lines check.
`Fault.answerUnmatched` is no target: an answer that names no request is the outside's mistake.

A step line's `assumes` lists the invariants the induction took as holding that this run did not prove: the violated ones, the undecided ones, and the ones `--only` left out.
An empty list means the verdict rests on no unproved invariant.

`Prove.violated` with `"from":"validState"` shows a state, an input, and the broken rules.
`cti_sound`: the state keeps the step invariant and every invariant, and the step Lean computes from it is the one the solver's terms describe.
`step_settled`: `after` is the state the step reaches before its invariant check.
The state need not be one a run reaches, because induction starts from any such state.

## prove: order of own steps and timers (T5)

Within one input, the own commands and queries that machines and reactions send wait in a queue, and the timers due at one deadline of a clock line fire one at a time.
The semantics runs both in a canonical order.
Two kinds of line check that no outcome depends on it:

- A pair line, `<first> and <second> commute`, asks for a state and two waiting own effects whose two orders end differently, with each effect keeping the ids it made.
- A timer line, `timers of <machine> fire forward`, asks whether the machine's `after` can set a timer before the current time.

`run_lines` (T5): take a run from the initial state whose inputs satisfy `validInputs`, and a cascade that one of its steps starts at a state and an input within the slots.
Where every state the cascade reaches in any order fits the slots, and every step line and pair line reads proved or within the bounds, every order of the cascade ends as the semantics' order does, up to renaming the ids the cascade made, or both orders fault.
Where every timer line reads proved, the same holds for the timers due at one deadline of a clock line.
The proof composes the commutation of one step with another, so a pair whose orders meet again only after later steps reads as not commuting.

A pair line's `assumes` holds exactly `"ids the service made are used only after they appeared on an out line"`.
Its `widened` names an own kind that a send with no handle or `on_answer` written in place makes.
Such a send stands for every handle or site of its type.

A violated pair or timer line rests on these theorems:

- `pair_violates`: a pair's counterexample in which one order faults or disables the other step, and the other order does not, is honest.
- `timer_violates`: a timer line's counterexample is a context whose `after` sets a timer before the current time.

A pair can also end undecided:

- `Undecided.upToRenaming`: the two orders the solver found different end the same once the ids the pair made are renamed.
- `Undecided.limit` with `"the two orders end with the same data but keep different functions, whose results are not compared"`.
- `Undecided.limit` when the two steps sent more requests than the renamings of wire ids that `prove` searches.

## prove: responses (T7)

A response states "after an event satisfying `after`, one satisfying `then` within `within` ms".
`prove` searches the runs from the initial state of 1 to `steps` inputs for one that violates it.
A response line never reads `Prove.proved`.

- `Prove.violated` shows the run as trace lines, with `"from":"init"` and `steps`. `response_sound`: the run's inputs satisfy `validInputs`, its clock lines are timely, and it violates the response.
- `Prove.withinBounds` lists the bounds and `{"bound":"steps"}`. `response_within` (T7), at each depth up to `steps`: no run of that many inputs within the slots, on which the line's `assumes` hold and at whose events the response's functions fit the slots, violates it.

A response is judged per step, so a `then` event in the same step as the `after` event counts.

## generate (T6)

`generate <root> <dir>` aims at each class of out line a service can show: `<command> accepted`, `<command> rejected <Variant>`, `<request> invalid <rule>`, `<query> answered`, `event <Variant>`, and `request <external>.<name>`.
`targets_cover`: every class of out line a step can show is aimed at by one of these targets.
For each target, `generate` searches runs from the initial state, one input longer each time, up to `steps` inputs.

- `Generate.reached` writes the trace of the shortest run it found to `<dir>/<service>/<target>.jsonl`. `generate_reaches` (T6): the written trace reads as the spec from the initial state, so `verify` replays it as passed unless it runs out of tries, and the last step of its run shows the target. `generate_sound`: every model the solver gives decodes to inputs that satisfy `validInputs` whose run faults nowhere and reaches the target. `targetFile_inj`: two targets never share a file, so no written trace overwrites another's.
- `Generate.unreached` exits 0. `generate_unreached` (T6b): no run of at most `steps` inputs within the slots, on which the line's `assumes` hold, shows the target's class at any step.

## verify

`verify <root> <dir>` replays each `.jsonl` trace in the directory against the spec.
Each `in` line runs as the spec's input.
The `out` lines up to the next `in` line form its window, which must hold the spec's `out` lines in some order.
The implementation names its ids and request ids its own way.
One binding, one to one, names the spec's ids by the trace's names, each from its first appearance on an `out` line.
An id that an `in` line names before any `out` line showed it is an id from outside the service.

`replay_iff`: unless `verify` runs out of tries, it prints `Verify.passed` exactly when some binding reads every window as the spec's.
After 100,000 tries it prints `Undecided.limit` and exits 2.

## Assumptions

Three assumptions appear in `assumes`, in these words.
`Assumption.text` in `Semantics/Valid.lean` defines each text beside its meaning, so the two cannot part.

| Text in `assumes` | Lines that print it |
| --- | --- |
| `ids the service made are used only after they appeared on an out line` | pair lines, responses, `Generate.unreached` |
| `no step of the run faults` | responses, `Generate.unreached` |
| `no clock line moves time past a timer that waits` | responses |

The first leaves ids from outside the service unrestricted.
Guarding against a guessed id is the implementation's job.

The model itself assumes more, and no line prints it:

- An implementation finishes an input before the next `in` line: all of an input's `out` lines come before the next `in` line. Inside a step, the cascade runs to completion.
- Time moves and timers fire only on clock lines (`{"in":"clock"}`). A trace that wants a timer to fire writes a clock line.
- State is durable. The inputs are requests, answers, events, and clock lines, with no restart. To specify a restart that loses state, write the loss as an event from a declared external.
- Every value a spec stores or sends can be written down: `Illegal.wireType` and `Illegal.stateType` reject functions and fresh-id sources there.

## Trusted base

You trust these programs and documents.
Everything between them is proved or checked.

- Gleam: `gleam build` type-checks the spec before the converter reads it.
- glance: the converter parses each module with it. On every conversion, the converter prints the IR back as Gleam and compares what glance reads from that text with what it read from the source.
- The Lean kernel checks every proof, and the Lean compiler builds the engine. Where compiled code uses a faster form, a root proves the two equal: `SExp.print_eq_printFast`, `Term.denote_eq_denoteFast`, `Term.beq_eq_beqFast`, and `Defs.add_eq_addFast`.
- Lean's JSON printer and parser stand between wire values and a trace's text.
- Z3: an unsat answer is trusted. A sat answer is not: Lean decodes the model and recomputes the counterexample or replays the run. The answer cache, keyed by SHA-256 digests of the script and of the solver's version, holds answers you trust in the same way.
- SMT-LIB: `Term.denote` states the standard's meaning of each term, and you trust that Z3 implements it. Division and remainder by 0 are free in the model, as the standard leaves them.

## Not guaranteed

- `Prove.proved` covers every run only by an induction no root states. `fault_sound` speaks of states within the slots, and the bound questions say that no step leaves them. That the two together cover every reachable state is not yet a theorem.
- A violated pair line whose two orders both finish with different states rests on Lean's search over renamings of request ids. `pair_violates` does not cover that case.
- `Generate.unreached` does not mean unreachable. A longer run or more slots may reach the target.
- A snapshot is not proved to replay as passed in `verify`. Only `generate`'s traces carry that theorem.
- The `bounds` list over-states lists. Every list type of the layout appears with its longest literal, though a list that only literals build cannot grow.
- SMT-LIB strings hold code points up to U+2FFFF. A string literal above that is `Undecided.unencodableString`. Lean's model of a string holds any code point, so an unsat answer about inputs whose strings go above U+2FFFF rests on Z3 beyond its string domain.
- `Undecided.unknown` comes from Z3 answering unknown, which its fixed resource limit and seeds make repeatable, or from a 30-second wall-clock limit, which depends on the machine.
- Ids that cannot be guessed, authentication, and anything else outside the spec's values are the implementation's concern.
