# Concepts

This page explains why tazuna's rules are what they are, and the model a spec describes.
[Guarantees](guarantees.md) states what each command proves.
`gleam run -m tazuna -- explain <kind>` says what one kind of output line means.

## Lean alone gives a spec its meaning

You write a spec in Gleam.
The launcher converts its modules to an IR, and the Lean engine gives the IR its meaning.
It runs the IR for `test`, `verify`, and `generate`, and encodes it as SMT-LIB for `prove` and `generate`.
Gleam never runs a spec's meaning, so the bodies of tazuna's built-ins only panic.
Trust flows one way, from Gleam to the IR to Lean to the solver, and no second interpreter can disagree with the definitions the theorems are about.

Where Gleam's two targets differ, Lean follows the Erlang target.
An `Int` has no bound, division truncates, and `x / 0` is 0 (`Gleam.div_zero` and the other `Gleam.*` roots).

## tazuna owns only what it can run, encode exactly, and prove

A construct belongs in a spec only if Lean can run it, encode it exactly as SMT, and prove the encoding.
The converter reports anything else as a `Restricted.*` line that names the construct, such as a `Float` or a recursive function.
Domain knowledge stays outside the spec, in an external service or in the input.

That rule shapes the values a spec holds:

- Numbers are integers. Hold an amount in its smallest unit, such as cents.
- An `Instant` and a `Duration` are milliseconds.
- A `Date` is a day with no calendar. A spec adds days and counts the days between two dates, and converts neither between instants and dates nor between time zones. Ask an external for a business day.
- A `String` supports `==`, `<>`, and `tazuna.length`, which counts code points. Its code points stop at U+2FFFF, as SMT strings do.

## The spec writes every order

For the inputs of any log, the spec gives exactly one set of outputs.
That makes the spec a test oracle, and `verify` can compare an implementation's log with it.
If an outcome depended on an order nobody wrote, the spec and an implementation could disagree for a reason nobody wrote down.

So a spec cannot read an order it does not own:

- A `Bag` is a multiset and offers no order to read. `bag.min_by` and `bag.max_by` return `Error(Tie)` instead of picking one of two equal items.
- A `Table` maps keys to values, with at most one value per key.
- Out lines and pending requests are multisets, and ids are compared up to renaming.

The engine still computes in one fixed order: machines and reactions in declaration order, a machine's instances by key, own commands in queue order, and timers due at one deadline one at a time.
`prove`'s pair and timer lines check that no outcome depends on that order.
A pair whose orders differ is a violation in the spec, and the fix writes the order into the spec.

## Explicit over implicit

Everything a verdict depends on appears in the spec or in the output:

- The spec writes its bounds. No command-line flag changes them, so the spec under review is the scope of every verdict.
- A verdict prints what it assumes in `assumes`.
- An undecided line says why it has no verdict, such as the solver's answer or the limit a search hit.
- No counterexample within the bounds is a success, `Prove.withinBounds`, as Alloy reports no counterexample within its scope. Otherwise every spec with a growing table would exit 2.
- `generate` says unreached, never unreachable. `prove` says `Prove.unreachable` only where every input kind's one-step question proves that no reachable step shows the class.

## Illegal states are unrepresentable

Types and structure come first, then proof, then tests.
`check` turns what Gleam's types cannot say into `Illegal.*` rules.
A wire name is a string literal written once, a type that crosses the wire holds no function, and a machine's key type has an order the solver can encode.

tazuna applies the same rule to itself.
Every kind of output line is a constructor of one Lean type.
`explain` is total over it, the theorems it names must be roots of `Axioms.lean`, and `test/e2e` holds one case per kind.

## The spec model

A spec is a list of services and the externals they talk to.
A service has:

- records, starting at `init`, and events, which `apply` folds into the records. Events are the only writes.
- commands. A caller outside `callers`, or input that breaks an `accepts` rule, makes the request invalid. `decide` accepts with events or rejects with a reason, and `ensures` states what must hold after the events.
- queries, which answer from the records, write nothing, and make no ids.
- machines and reactions, which react to each event.
- invariants and responses, which `prove` checks.
- bounds and scenarios.

A step takes one input and gives one outcome: accepted, answered, rejected, invalid, or fault.
A fault is a bug in the spec, never a rejection: a broken invariant or `ensures` rule, more internal steps than `cascade`, an own effect that asks for what its target does not accept, or an answer that names no pending request.
A step that faults leaves the state as it was.

Inside a step the cascade runs to completion.
Each event is applied, then every machine instance and reaction reacts to it.
A request to an external goes out at once and waits as a pending request until an answer names it.
A command or query of the service's own waits in a queue and runs as one internal step.

A machine has one instance per key that its `instances` function returns from the records.
On each event an instance stays or enters a state.
`after` may set a timer, which enters its state when a clock line reaches its deadline, and entering a state may start an effect.

A command makes new ids with `tazuna.fresh` from its context.
An `Id` compares with `==` only, and an id from outside the service comes by its name.
An external is a service outside the spec, known by the commands, queries, and events it declares.

A scenario is a list of steps from `init` at time 0, and `test` compares its run with a snapshot.

## Traces

Snapshots, `generate`'s output, and `verify`'s input share one format of JSON lines.
A header line names the service.
Each later line is an input (`in`) or an output (`out`) of the service, with the service's time in milliseconds:

```json
{"service":"counter","trace":1}
{"caller":{"tag":"User"},"id":"1","in":"request","input":5,"name":"add","time":0}
{"out":"answer","outcome":"accepted","time":0,"to":"1"}
{"out":"event","time":0,"value":{"amount":5,"tag":"Added"}}
{"in":"clock","time":10}
{"external":"mail","id":"r1","input":6,"name":"send","out":"request","time":10}
{"in":"answer","ok":null,"time":10,"to":"r1"}
```

The inputs are requests, answers to the service's requests, subscribed events, and clock lines.
A custom type's value is an object whose `tag` names the variant.
A bag or a table is an array, and a date is its ISO 8601 label.
A trace names fresh ids `id1`, `id2`, and the service's requests `r1`, `r2`, in the order they first appear.
An implementation names them its own way, and `verify` binds its names to the spec's ids.

The `out` lines after an `in` line, up to the next one, form its window.
`verify` compares each window as a multiset, so the order in which an implementation writes a window never decides the verdict.

## A counterexample is a decision about the spec

`prove` checks an invariant by induction.
It holds in the initial state, and each step from any state within the bounds where every invariant holds keeps it.
That second part also starts from states no run reaches, so a counterexample with `"from":"validState"` is one of two things:

- A real bug. Fix the behavior.
- A state no run reaches. State the fact that rules it out as another invariant.

## Each command reports one kind of mistake

- `check` reports the structure of the spec.
- `test` reports what a scenario's run shows against its snapshot.
- `prove` reports what holds in every state within the bounds.
- `generate` writes inputs that reach each class of out line, for an implementation's tests.
- `verify` reports what an implementation's log shows.

Every command writes JSON lines to stdout, its errors included, because the usual reader is a program or a coding agent.
tazuna transforms a result only when a later step needs it, and never only for readability, so it does not shrink a counterexample.

## Exit codes

A command exits with the code of its worst line:

| Code | Meaning |
| --- | --- |
| 0 | Every line is a success. `Prove.withinBounds`, `Prove.unreachable` and `Generate.unreached` count. |
| 1 | A line is a violation. |
| 2 | A line is undecided and none is a violation. |
| 3 | The command did not run as asked, for a usage or system error. The spec is not judged. |
| 4 | tazuna has a bug. No spec reaches it. |

`explain` prints each kind's exit code.
