# Guarantees

This page states what a passing `check`, `test`, or `verify` tells you, which side fixes a violation, which reports cover only some cases, and the assumptions that the results depend on.
Lean definitions state what a spec means, and Lean theorems prove properties of that meaning.
tazuna guarantees only what the Lean theorems prove.

Precedent: AWS Cedar, whose properties are proven in Lean and whose Rust implementation is tested against the Lean model.

## Terms

A *spec* defines services.
A service interacts with the world only through messages.
It receives requests (commands, queries, and subscriptions), events from other services, user operations on its screens, the current time, and restarts from its environment.
It sends answers, events, and requests of its own.
The sequence of these messages, each with its time, is the service's *trace*.

A *scenario* is a sequence of inputs to one service.
tazuna has three tools that report violations:

- `check` reads the spec and reports its violations without running it.
- `test` runs every scenario and compares its trace with the scenario's *snapshot*, the trace saved from an earlier run.
- `verify` compares the traces that an implementation records for the scenarios with the snapshots.

A *violation* is a problem that a tool reports.
Each violation has a kind, such as `Fault.failedEnsures`.
The part of the kind before the dot is the violation's *group*.
A kind's name and data, with its doc comment where they do not suffice, state what the kind means.
A run stops at a violation of a *halting* kind, because the behavior after that violation is undefined.

## What a passing tool means

A tool *passes* when it reports no violation.

- When `check` passes, the spec type-checks and has no violation of the groups that `check` reports.
- When `test` passes, `check` passes, and each scenario's trace equals its snapshot.
- When `test` and `verify` both pass with the same spec and snapshots, the trace that the implementation records for each scenario matches its snapshot.

When, in addition, the [assumptions](#assumptions) hold, the implementation sends the messages that the spec defines for the inputs of each scenario.
tazuna guarantees nothing about inputs that no scenario contains.

### When a trace matches a snapshot

A trace *matches* a snapshot when both have the same inputs and the outputs between two consecutive inputs pair up one to one.
Paired outputs have equal type, target, time, and value.
The pairing keeps exactly the orders that the snapshot states.

`verify` compares the IDs and keys that the implementation chooses up to a one-to-one renaming.
A key that the spec creates is renamed from the output that creates it; before that output, `verify` compares it as written.
`verify` compares the IDs of the requests that the implementation sends only through the answers that name them.
When a line of a trace is malformed, `verify` reports it and compares nothing after it.

## Who fixes a violation

The side that breaks a contract is at fault: the caller for a precondition, and the callee for a postcondition.
A definition's *contract* is what it promises to its callers: its inputs and outputs, its preconditions (`requires`), its postconditions (`ensures`), and its rejections.
The following table names the side at fault for each group.

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

An implementation's *recorder* writes the messages that the implementation receives and sends as a trace.
A *replay* gives the implementation the inputs of a scenario.

Precedent: Design by Contract (Bertrand Meyer), where a precondition binds the caller and a postcondition binds the callee.

## Detections

A *detection* is a report that does not cover every case.
When a detection reports a problem, the problem is real.
When a detection reports nothing, the problem can still exist.

`test` explores paths that append inputs to each scenario.
An explored path uses values from the scenarios and new IDs, and it neither resends a command nor redelivers an event.
The detections are:

- Violations that `test` finds on explored paths.
- `Restricted`.
- `OrderDependent` and `ChoiceDependent`.
- `InvalidInput`.
- `Uncovered`.

## Assumptions

The guarantees hold only under the following assumptions.
tazuna detects breaks of each assumption only partly or not at all.

- **Runtime.** The TypeScript runtime returns the same traces and violations as the Lean definitions.
  The runtime and the Lean definitions are compared only on tazuna's own example specs and traces, not on yours.
  For `test`, the comparison covers the example scenarios and the paths that append up to two inputs to them.
  For `check` and `verify`, it covers the example specs and traces.
- **Spec functions.** Spec functions are deterministic: they read no clock, random source, or mutable global state, and receive the current time as an argument.
- **Types.** Each value in spec code has the type that the code declares.
- **Recorder.** The recorder writes only messages that the implementation received or sent, with the values that the implementation used, and it writes the time of each message correctly.
  An input line therefore carries the implementation's IDs and keys, not the snapshot's.
  `verify` reports a message that the recorder leaves out.
- **External services.** Each external service keeps the contract that the spec assumes of it.
  `verify` detects a break of this assumption only on the traces that the recorder writes.
- **Other services.** The messages from another service of the spec that a scenario gives as inputs are messages that the other service sends at the times that the scenario gives.
  `test` detects only the messages that break the other service's contract.
- **Tools.** The Lean kernel, the TypeScript type checker, and Node.js are correct.

## Proven properties

Each section lists properties that hold for every spec.

Machines and screens are statecharts, called *charts*.
A running chart is an *instance*.
A map state has one *copy* of its child states for each key of its items.

### Observable behavior

- A spec defines behavior by traces alone.
  The records and instances of a service are internal, so an implementation can store its state in any form.
- When `check` passes, each contract lists only the members of its own service.
- When `check` passes, a chart sends queries only to other services.

Precedent: I/O automata (Nancy Lynch and Mark Tuttle), whose external behavior is the sequence of input and output actions.

### Data validity

- Before sending, the service normalizes the payload of each event that a command emits and the output of each query answer with the declared schema.
- An accepted command emits only the events that the command lists in its `emits`.
  When `check` passes, these are events of the command's own service.
- When the input of a command or query does not fit its schema, the service rejects it with `invalid-input`.

Precedent: "Parse, don't validate" (Alexis King), where a value is checked once at the boundary and trusted inside.

### Statecharts

- Entering a compound state enters its initial child.
- A transition exits states from the innermost and enters states from the outermost.
- In each atomic state, at most one transition runs for one event.
- When a transition of a state and a transition of its ancestor are both enabled, the transition of the state runs.
- A transition to an ancestor exits the ancestor.
- A transition that reenters its source exits the source first, and a transition that does not reenter keeps it.
- An event that enables no transition changes nothing.
- A stopped instance processes no event.
- An event without a key reaches every copy of a map state.
- When the copies of a map state have distinct keys, an event with a key reaches at most one copy.

Precedent: SCXML (W3C), whose algorithm fixes the entry and exit order and the conflict resolution of transitions.

### Requests and deadlines of a state

- A deadline fires only while its state is active.
- Leaving a state makes its awaited requests and queued commands stale.
- An answer to a stale request changes nothing.
- A state that is exited before it sends its requests sends nothing.
- Stopping an instance cancels the deadlines and requests of its active states.

Precedent: SCXML (W3C), which cancels an invoked service when the state that invoked it is exited.

### Subscriptions and screens

- The service sends a new answer to a subscription only when the answer changes.
- The service sends no answer to an ended subscription.
- Opening a screen creates one child instance of the opened screen.
- An operation reaches a screen only when no modal screen that was opened later is still open.
- A non-modal child screen leaves its parent operable.

Precedent: the modal dialog of the WAI-ARIA Authoring Practices (W3C), which makes the content outside the dialog inert.

### Time

- The current time is an input.
- Each input carries the time at which it arrives.
- When the time of an input goes back, `test` reports it under `InvalidInput`.
- A deadline fires when the input time reaches it.

Precedent: deterministic simulation testing (FoundationDB), where the simulator supplies the clock.

### Processing and completion

- A service processes one message to completion before it takes the next one.
- A command's postconditions and the entity invariants hold for the records after the command ends.
- A rejected command writes no record and emits no event.
- An accepted command writes its records before any reaction to its events runs.
- The processing of one message ends within the limits that tazuna sets, or halts with the `Fault` of the exceeded limit.

Precedent: the run-to-completion step of UML state machines (OMG).

### Ordering and determinism

- The result of a spec depends only on its inputs and on the orders that the spec states.
- Spec functions see the records of an entity in key order, regardless of the order in which they were written.
- An array sorted by a key keeps the order of equal keys.
- Deadlines due at the same time fire in a default order, and the exploration of `test` also tries the other orders.

Precedent: CHESS (Madanlal Musuvathi and others), which makes each scheduling choice an input to a run.

### Identity

- No two records of a keyed entity share a key.
- A reference from one record to another resolves to an existing record.
- When a reference does not resolve, `test` reports it under `Fault`.
- When a command arrives again with the same ID and the same input, the service answers it with the first answer and does not run it again.
- The service rejects a command that reuses an ID with a different input.
- When an event arrives again with the same ID, the service does not process it again.
- When an event arrives again with the same ID and a changed payload, `test` reports it under `InvalidInput`.
- The service answers a repeated query again, because a query has no identity.

Precedent: the `Idempotency-Key` HTTP header (IETF).

### Restart

- After a restart, a service keeps its records, its command answers, its delivered events, and its created keys.
- A restart discards the instances, deadlines, awaited requests, and subscriptions of the service.

Precedent: the Restart action of the Raft TLA+ spec (Diego Ongaro).
