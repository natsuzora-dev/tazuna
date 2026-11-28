# Concepts

This page explains why tazuna's rules are what they are, and the model a spec describes.
[Guarantees](guarantees.md) states what each command proves.
`gleam run -m tazuna -- explain <kind>` says what one kind of output line means.

## Lean alone gives a spec its meaning

You write a spec in Gleam.
The launcher converts its modules to an IR, and the Lean engine gives the IR its meaning.
It runs the IR for `test`, `verify`, `explore`, and `search`, and encodes it as SMT-LIB for `prove` and `search`.
Gleam never runs a spec's meaning, so the bodies of tazuna's built-ins only panic.
Trust flows one way, from Gleam to the IR to Lean to the solver, and no second interpreter can disagree with the definitions the theorems are about.

tazuna runs on Gleam's Erlang target, and where targets differ, Lean follows it.
An `Int` has no bound, division truncates, and `x / 0` is 0 (`Gleam.div_zero` and the other `Gleam.*` roots).

## tazuna owns only what it can run, encode exactly, and prove

A construct belongs in a spec only if Lean can run it, encode it exactly as SMT, and prove the encoding.
The converter reports anything else as a `Restricted.*` line that names the construct, such as a `Float` or a recursive function.
Domain knowledge stays outside the spec, in an external service or in the input.

That rule shapes the values a spec holds:

- Numbers are integers. Hold an amount in its smallest unit, such as cents.
- An `Instant`, from `tazuna/instant`, is a point in time to the millisecond that a spec cannot write. It comes from a context's `now` or from an input, and `instant.add`, `instant.diff`, `instant.is_before` and `instant.is_after` move and compare it. So moving every instant by the same amount changes no outcome, and a record that has no instant at `init` holds an `Option(Instant)`.
- A `Duration`, from `tazuna/duration`, is a length of time. Only `duration.milliseconds`, `seconds`, `minutes` and `hours` make one, so every length a spec writes names its unit. `instant.add` moves an instant by a duration, `instant.diff` gives the duration between two, and `duration.to_milliseconds` reads one as an `Int`.
- A `Date` is a day with no calendar. A spec adds days and counts the days between two dates, and converts neither between instants and dates nor between time zones. Ask an external for a business day.
- A `String` supports `==`, `<>`, and `tazuna.length`, which counts code points. Its code points stop at U+2FFFF, as SMT strings do. A string that `prove` or `search` picks keeps only what the spec asks of it, so it may read as a literal of the spec with letters added.

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
A pair whose orders differ, in a state a run reaches, is a bug in the spec, and the fix writes the order into the spec.

## Explicit over implicit

Everything a verdict depends on appears in the spec or in the output:

- Meaning and scope live apart. `spec()` holds only what the spec means. A model function beside it, such as `pub fn model() -> tazuna.Model`, holds the scope `prove`, `explore` and `search` check it in: the slots, how deep `explore` looks and which values it tries, how long a run `search` unrolls gets, and the solver's resource limit. A root module may define any number of models, as a TLA+ spec has many `.cfg` files and an Alloy module many `run` commands, and `--model <name>` picks one. Every line whose verdict rests on the scope names the model and the values it read. No other flag changes the scope; `--timeout` only stops the run.
- A verdict prints what it assumes in `assumes`.
- An undecided line says why it has no verdict, such as the solver's answer or the limit a search hit.
- No counterexample within the bounds is a success, `Prove.withinBounds`, as Alloy reports no counterexample within its scope. Otherwise every spec with a growing table would exit 2.
- `explore` and `search` say unreached, never unreachable, of what they did not reach. `Prove.unreachable` says unreachable only where every input kind's code or one-step question proves that no reachable step shows the class. Where that holds only within the slots, the line is `Prove.unreachableWithinBounds` instead, as `Prove.withinBounds` is to `Prove.proved`, so a bound that keeps a target out of reach never reads as the spec doing so.
- A step that breaks a target from a state where every invariant holds is `Prove.unproved`, not a violation: the state may be one no run reaches. Only the initial state or a run from it is a violation, as TLC reports one only with a behavior and Dafny says "might not hold" of a failed one-step proof.

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

- records, starting at `init`, and events, which `apply` folds into the records at the step's time. Events are the only writes, so a time the records keep, such as a deadline, is written in `apply` from `ctx.now`.
- commands. `callers` lists who may send one: `Outside(caller)` for a request line from that caller, and `Own` for the service's own machines and reactions. An origin outside `callers`, or input that breaks an `accepts` rule, makes the request invalid. `decide` accepts with events or rejects with a reason, and `ensures` states what must hold after the events.
- queries, which answer from the records, write nothing, and make no ids.
- machines and reactions, which react to each event.
- invariants and responses, which `prove` checks. A response says "after each event `trigger`, an event that answers it within `within` ms". Its `deadline` reads the deadline the records keep for a trigger that waits for its answer, so `prove` checks the response step by step, as it checks an invariant. Whatever answers a trigger must change what `deadline` reads.
- `cascade`, the most internal steps one input may take, and scenarios.

A step takes one input and gives one outcome: accepted, answered, rejected, invalid, or fault.
A fault is a bug in the spec, never a rejection: a broken invariant or `ensures` rule, more internal steps than `cascade`, an own effect that asks for what its target does not accept, or an answer that names no pending request.
A step that faults leaves the state as it was.

Inside a step the cascade runs to completion.
Each event is applied, then every machine instance and reaction reacts to it.
A request to an external goes out at once and waits as a pending request until an answer names it.
A command or query of the service's own waits in a queue and runs as one internal step.

A machine has one instance per key that its `instances` function returns from the records.
On each event an instance stays or enters a state.
`timer` gives the timer an instance waits for, read off its state and the records: a clock line at or after the timer's `at` enters the timer's state.
`timer` sees no time, so a deadline is a time the records keep, and a timer whose time has passed fires at the next clock line.
Entering a state may start an effect.

A command makes new ids with `tazuna.fresh` from its context.
An `Id` compares with `==` only, and an id from outside the service comes by its name.
Where `prove`, `explore` or `search` picks an id from outside, it names it by a number, in the order of ids: `0`, `7`, `~42`, and `-8` for one before `0`.
An external is a service outside the spec, known by the commands, queries, and events it declares.

A scenario is a list of steps from `init` at time 0, and `test` compares its run with a snapshot.

## Traces

Snapshots, the traces `explore` and `search` write, and `verify`'s input share one format of JSON lines.
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
A response is checked the same way, one step at a time against the deadlines the records keep.
That second part also starts from states no run reaches, so a counterexample with `"from":"validState"` is one of two things:

- A real bug. Fix the behavior.
- A state no run reaches. State the fact that rules it out as another invariant.

## Each command reports one kind of mistake

- `check` reports the structure of the spec.
- `test` reports what a scenario's run shows against its snapshot.
- `prove` reports what holds in every state within the bounds.
- `explore` and `search` report runs that break a target `prove` left open, and write runs that reach each class of out line, for an implementation's tests. Each runs the stages before it, so its output holds theirs.
- `verify` reports what an implementation's log shows.

Every command writes JSON lines to stdout, its errors included, because the usual reader is a program or a coding agent.
tazuna transforms a result only when a later step needs it, and never only for readability, so it does not shrink a counterexample.

## Exit codes

A command exits with the code of its worst line:

| Code | Meaning |
| --- | --- |
| 0 | Every line is a success. `Prove.withinBounds`, `Prove.unreachable`, `Prove.unreachableWithinBounds`, `Explore.unreached`, `Explore.notViolated` and `Search.unreached` count. |
| 1 | A line is a violation: the initial state or a run from it breaks a target. |
| 2 | A line is not settled and none is a violation: undecided, `Prove.unproved` or `Search.unsettled`. |
| 3 | The command did not run as asked, for a usage or system error. The spec is not judged. |
| 4 | tazuna has a bug. No spec reaches it. |
| 5 | The run's `--timeout` passed first. Its last line, `Run.unfinished`, lists the targets it left; a violation printed before it still stands. Codes 3 and 4 outrank it. |

`explain` prints each kind's exit code.
