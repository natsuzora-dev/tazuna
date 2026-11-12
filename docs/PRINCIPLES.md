# tazuna principles

This document states what tazuna guarantees, what the guarantees assume, and the principles of the spec language.
It holds only the facts that apply across tazuna.
Every other fact is in the doc comment of the definition that the fact is about.

## Terms

A *spec* defines services.
A service interacts with the world only through messages.
It receives requests (commands, queries, and subscriptions), events from other services, user operations on its screens, the current time, and restarts from its environment.
It sends answers, events, and requests of its own.
The sequence of these messages, each with its time, is the service's *trace*.

A *chart* is a statechart that a spec defines.
A *machine* is a running instance of a chart.

A definition's *contract* is what it promises to its callers: its inputs and outputs, its preconditions (`requires`), its postconditions (`ensures`), and its rejections.

A *scenario* is a sequence of inputs to one service.
tazuna has three tools:

- `check` reads the spec and reports its violations without running it.
- `test` runs every scenario and compares its trace with the scenario's *snapshot*.
  With `--update`, `test` writes the trace as the snapshot instead.
- `verify` compares the traces that an implementation records for the scenarios with the snapshots.

An implementation's *recorder* writes the messages that the implementation receives and sends as a trace.
A *replay* gives the implementation the inputs of a scenario.

When a tool finds an error, it reports a *violation*.
Each violation has a kind, such as `Fault.failedEnsures`.
The part of the kind before the dot is the violation's *group*.
The type that declares a group states what its violations mean.
Some kinds *halt* the run: the run stops at such a violation, because the behavior after it is undefined.

## Where the meaning lives

Lean definitions state what a spec means, and Lean theorems prove properties of that meaning.
tazuna guarantees only what the Lean theorems prove.

Precedent: AWS Cedar, whose properties are proven in Lean and whose Rust implementation is tested against the Lean model.

## What passing means

A tool *passes* when it reports no violation.

- When `check` passes, the spec type-checks.
- When `test` passes, `check` passes, and each scenario's trace equals its snapshot.
- When `test` and `verify` both pass with the same spec and snapshots, the trace that the implementation records for each scenario matches its snapshot.

A trace *matches* a snapshot when both have the same inputs and the outputs between two consecutive inputs pair up one to one.
Paired outputs have equal type, target, time, and value.
The pairing keeps exactly the orders that the snapshot states.
`verify` compares the IDs and keys that the implementation chooses up to a one-to-one renaming.
An implementation value that equals the snapshot value matches it even where the renaming gives another value.
`verify` compares the IDs of the requests that the implementation sends only through the answers that name them.
When a line of a trace is malformed, `verify` reports it and compares nothing after it.

A passing `verify` implies a match only when the following conditions hold:

- No ID repeats within the snapshot, and no ID repeats within the recorded trace.
  A scenario that resends a command or redelivers an event with the same ID breaks this condition.
- The implementation does not answer a request that it sent itself.
- No subscription that the service opens has an unordered collection in its input.

Under the assumptions below, when `test` and `verify` pass, the implementation sends the messages that the spec defines for the inputs of each scenario.
tazuna guarantees nothing about inputs that no scenario contains.

### Detections

A *detection* is a report that does not cover every case.
When a detection reports a problem, the problem is real.
When a detection reports nothing, the problem can still exist.
The detections are:

- the violations that `test` finds on explored paths.
  An explored path appends up to `--depth` inputs to a scenario.
  It uses values from the scenarios and new IDs, and it neither resends a command nor redelivers an event.
- `Restricted`, which reports spec code that reads a source that the assumptions exclude.
- `OrderDependent` and `ChoiceDependent`, which report a result that depends on an order or a choice that nobody controls, in the cases that their types list.
- `InvalidInput`, which reports an input that the environment could not give, such as an answer to a request that nobody awaits.
- `Uncovered`, which reports the parts of commands, queries, automations, and charts that no run reaches.

### Groups

A caller that breaks a precondition is at fault, and a callee that breaks a postcondition is at fault.
The following table names the side at fault for each group, so that the reader knows which side to fix.

Precedent: Design by Contract in Eiffel (Meyer).

| Group | Reported by | Side at fault |
|---|---|---|
| `Malformed` | `check` | The spec. |
| `NonCanonical` | `check` | The spec. |
| `Restricted` | `check` | The spec. |
| `Illegal` | `check` | The spec. |
| `InvalidInput` | `test` | The scenario: an input that the environment could not give, including an answer of an external service that breaks the contract that the spec assumes of it. |
| `Fault` | `test` | The spec. |
| `OrderDependent` | `test` | The spec. |
| `ChoiceDependent` | `test` | The spec. |
| `Uncovered` | `test --coverage` | The scenarios. |
| `Mismatch` | `test`, `verify` | The implementation or external service whose trace differs, or, for `test`, the snapshot that differs from its scenario's run. |
| `Uncomparable` | `test`, `verify` | The recorder or replay whose trace inputs differ from the scenario's, or, for `test`, the snapshot that has no scenario. |

## Assumptions

The guarantees hold under the following assumptions.
tazuna checks each assumption only partly or not at all.

- **Runtime.** The TypeScript runtime returns the same traces and violations as the Lean definitions.
  The two are compared only on tazuna's own example specs and traces, not on yours: for `test`, on the example scenarios and the paths that append up to two inputs to them; for `check` and `verify`, on the example specs and traces.
- **Spec functions.** Spec functions are deterministic: they read no clock, random source, or mutable global state, and receive the current time as an argument.
- **Types.** Each value in spec code has the type that the code declares.
- **Recorder.** The recorder writes only messages that the implementation sent, and it writes the time of each message correctly.
  `verify` reports a message that the recorder leaves out.
- **External services.** Each external service keeps the contract that the spec assumes of it.
  `verify` checks this assumption only on the traces that the recorder writes.
- **Other services.** The messages that a scenario takes from another service of the spec are messages that the other service sends at the time that the scenario gives.
  `test` checks only that they keep the other service's contract.
- **Tools.** The Lean kernel, the TypeScript type checker, and Node.js are correct.

## What tazuna guarantees

### Observable behavior

- A spec defines behavior by traces alone.
  The records and machines of a service are internal, so an implementation can store its state in any form.
- When `check` passes, each contract lists only the members of its own service.
- When `check` passes, a chart sends queries only to other services.

Precedent: the I/O automata of Lynch and Tuttle, whose external behavior is the sequence of input and output actions.

### Data validity

- Before sending, the service normalizes the payload of each event that a command emits, and the output of each query answer, with the declared schema.
- An accepted command emits only the events that the command lists in its `emits`.
  When `check` passes, these are events of the command's own service.
- The service rejects a command or query whose input does not fit its schema with `invalid-input`.

Precedent: "Parse, don't validate" (Alexis King), where a value is checked once at the boundary and trusted inside.

### Statecharts

- Entering a compound state enters its initial child.
- A transition enters states from the outermost and exits them from the innermost.
- In each atomic state, at most one transition runs for one event.
- When transitions of a state and of its ancestor are enabled, the descendant's transition runs.
- A transition to an ancestor exits the ancestor.
- A transition that reenters its source exits the source first, and a transition that does not reenter keeps it.
- An event that enables no transition changes nothing.
- A stopped machine processes no event.
- An event without a key reaches every copy of a map state.
- When the copies of a map state have distinct keys, an event with a key reaches at most one copy.

Precedent: SCXML (W3C), whose algorithm fixes the entry and exit order and the conflict resolution of transitions.

### Work of a state

- A deadline fires only while its state is active.
- Leaving a state makes its awaited requests and queued commands stale.
- An answer to a stale request changes nothing.
- A state that is exited before it sends its requests sends nothing.
- Stopping a machine cancels the deadlines and requests of its active states.

Precedent: SCXML, which cancels an invoked service when the state that invoked it is exited.

### Subscriptions and screens

- The service sends a new answer to a subscription only when the answer changes.
- The service sends no answer to an ended subscription.
- Opening a screen adds one child screen.
- An operation reaches a screen only when no modal screen covers the screen.
- A non-modal child screen leaves its parent operable.

Precedent: the modal dialog of the WAI-ARIA Authoring Practices, which makes the content outside the dialog inert.

### Time

- The current time is an input.
- Each input carries the time at which it arrives, and `test` reports an input whose time goes back under `InvalidInput`.
- A deadline fires when the input time reaches it.

Precedent: the deterministic simulation testing of FoundationDB, where the simulator supplies the clock.

### Processing and completion

- A service processes one message to completion before it takes the next one.
- A command's postconditions and the entity invariants hold for the records that the command leaves.
- A rejected command writes no record and emits no event.
- An accepted command writes its records before any reaction to its events runs.
- The processing of one message ends within the limits, or halts at the limit under `Fault`.

Precedent: the run-to-completion step of UML state machines.

### Ordering and determinism

- The result of a spec depends only on its inputs and on the orders that the spec states.
- Spec functions see the records of an entity in key order, regardless of the order in which they were written.
- An array sorted by a key keeps the order of equal keys.
- Deadlines due at the same time fire in a default order, and the input's `deadlineOrder` field can choose another order.

Precedent: CHESS (Musuvathi and others), which makes each scheduling choice an input to a run.

### Identity

- No two records of a keyed entity share a key.
- A reference from one record to another resolves, and `test` reports one that does not under `Fault`.
- When a command arrives again with the same ID and the same input, the service answers it with the first answer and does not run it again.
- The service rejects a command that reuses an ID with a different input.
- When an event arrives again with the same ID, the service does not process it again, and `test` reports a changed payload under `InvalidInput`.
- The service answers a repeated query again, because a query has no identity.

Precedent: the `Idempotency-Key` HTTP header of the IETF.

### Restart

- After a restart, a service keeps its records, its command answers, its delivered events, and its created keys.
- A restart discards the machines, deadlines, awaited requests, and subscriptions of the service.

Precedent: the Restart action of the Raft TLA+ spec.

## How to write a spec

The following principles shape the language.
They are design rules, not guarantees.

### One explicit way

The language offers one way to write each meaning, and it requires you to write even the choice to do nothing, such as ignoring a rejection.
LLMs write tazuna specs, and one form per meaning removes variation and plausible omissions.
`check` reports the forms that `NonCanonical` lists.

Precedent: PEP 20, "There should be one-- and preferably only one --obvious way to do it" and "Explicit is better than implicit."

### Declared rejections

Each command and query declares the rejections that it can return.
A sender that can receive a rejection handles it or writes that it ignores it.
A sender that cannot receive a rejection cannot write a handler for it.
The TypeScript type checker rejects the handlers that the types show to be unreachable, and `check` reports the remaining ones under `NonCanonical`.

Precedent: Java's checked exceptions.

### No uncontrolled choice

A result must not depend on an order or a choice that nobody controls.
When more than one order can happen, the spec states the order, or an input chooses it.

Precedent: CHESS, as above.

### Reach every part

The run of some scenario reaches each part of a spec.
A part that no run reaches has no behavior that tazuna can compare.

### Reject wrong forms early

tazuna rejects a wrong form with the earliest tool that can detect it, in this order: the TypeScript type checker, `check`, `test`, and `verify`.
A wrong form that an earlier tool reports is cheaper to fix.

Precedent: Yaron Minsky's "make illegal states unrepresentable."

### Follow the standard

Where a standard defines a behavior, as for statecharts, request IDs, modal screens, and units, tazuna follows the standard.
Readers and implementers can then rely on what they already know.
