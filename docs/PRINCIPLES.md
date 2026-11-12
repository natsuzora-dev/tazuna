# tazuna principles

This document states the principles behind the design of tazuna.

This document holds only the facts that apply across tazuna and the facts that read better as a list.
Every other fact is in the doc comment of the definition that the fact is about.
Read those doc comments for details.

## Where the meaning lives

Lean definitions define what a spec means, and Lean theorems state the properties of that meaning.
The TypeScript runtime that the tools use runs the same specs and inputs as the Lean model, and tests compare the two results (differential testing, as in AWS Cedar).
The small specs, scenarios, and snapshots under `test/` are examples of this meaning.

A spec contains *scenarios*: sequences of inputs to one service.
The tools work on a spec as follows:

- `check` reads the spec without running it.
- `test` runs every scenario, and keeps the messages that each run receives and sends as a *snapshot*.
  It also runs every path that appends inputs to a scenario, up to the exploration depth.
  The appended inputs use values chosen from those that the scenarios write, and new IDs; `test` resends no command and redelivers no event.
- `verify` compares the messages that an implementation records for the same scenarios with the snapshots.

When a tool finds an error, it reports a *violation*.
Each violation has a kind, such as `Fault.failedEnsures`.
The part of the kind before the dot is the violation's *group*.
The type that declares a group states what its violations mean.

## What tazuna guards

Each of the following sections states a property in the vocabulary of its field, then how tazuna checks it, then one precedent.

### Observable behavior

A service interacts with the world only through messages.
It receives requests (commands, queries, and subscriptions), events from other services, user operations on its screens, the current time, and restarts by its environment.
It sends answers, events, and requests of its own.
The sequence of these messages, each with its time, is the service's *trace*.
A spec defines behavior by traces alone.
Two services behave the same when they produce the same trace for the same inputs (trace equivalence).
The records and states of a spec are internal, so an implementation can store its state in any form.
When the spec does not order the outputs of one input, an implementation can send them in any order, and only an order that the snapshot states is compared.

`check` reports spec code that reads another service's internals instead of exchanging messages with it under `Restricted` and `Illegal`.
`verify` reports a trace that differs from its snapshot under `Mismatch`, and a trace that it cannot compare with a snapshot under `Uncomparable`.

Precedent: the I/O automata of Lynch and Tuttle, whose external behavior is the sequence of input and output actions.

### Time as input

The current time is an input.
Each input carries the time at which it arrives, and time never goes back.
A deadline fires when the input time reaches it.
Spec functions receive the current time as an argument and never read a clock.

`check` reports a time or delay that the run cannot read as milliseconds under `Malformed`, and spec code that reads a clock under `Restricted`.
`test` reports an input whose time goes back under `InvalidInput`.

Precedent: the deterministic simulation testing of FoundationDB, where the simulator supplies the clock.

### Atomicity

A service processes one message to completion before it takes the next one.
No state during that processing is visible: the trace shows the message and then its outputs.
A command's postconditions and the entity invariants apply to the records that the command leaves.
A rejected command changes nothing: it writes no record and emits no event.
An accepted command writes its records before any reaction to its events runs.

`check` reports a cycle that would keep one message from completing under `Illegal`.
`test` reports a broken postcondition or invariant, and a message whose processing exceeds a limit, under `Fault`.

Precedent: the run-to-completion step of UML state machines.

### Ordering and determinism

The result of a spec depends only on its inputs and on the orders that the spec writes, such as the order of transitions, emitted events, array elements, and scenario inputs.
Spec functions are deterministic: they read no clock, random source, or global state.
When the spec writes no order and more than one order can happen, the run takes a default order, and a field of an input can choose another.
Examples are the order of two deadlines due at the same time, the request that an answer goes to, and the order of two processing steps within one message that nothing orders.
The same inputs, with the same choices, always give the same result.
A result must not depend on a choice that nobody controls.

`check` reports spec code that reads a nondeterministic source under `Restricted`.
`test` reports a result that depends on an order that the spec does not fix under `OrderDependent`, and a result that depends on a choice that nobody controls under `ChoiceDependent`.

Precedent: CHESS (Musuvathi and others), which makes each scheduling choice an input to a run.

### Identity and uniqueness

One name refers to one thing.
Within a service, a name refers to one definition, scenario, or `constants()` call, and each of them has one name.
Each record of a keyed entity has a key, and no two records of that entity share a key.
A reference from one record to another must resolve.
A request ID identifies one request.
A command that arrives again with the same ID and the same input gets its first answer and runs no second time.
A command that reuses an ID with a different input is rejected.
An event that arrives again with the same ID is not processed again, and its payload must not change.
A query has no such identity: the service answers it again.

`check` reports a name that refers to more than one thing, or a thing with more than one name, under `Malformed`.
`test` reports a reference that does not resolve under `Fault`, and a redelivered event whose payload changed under `InvalidInput`.

Precedent: the `Idempotency-Key` HTTP header of the IETF.

### Failure handling

Each command and query declares the rejections that it can return.
A sender that can receive a rejection handles it, or writes that it ignores it.
A sender that cannot receive a rejection cannot write a handler for one.
When a spec definition breaks the meaning during a run, the run reports it, and when the behavior after that point is undefined, the run stops there.

The TypeScript type checker rejects a rejection handler that the types show to be unreachable, and `check` reports the remaining missing or unreachable handlers under `NonCanonical`.
`test` reports a definition that breaks the meaning under `Fault`.

Precedent: Java's checked exceptions, where a caller handles or declares each exception that a method declares, and a `catch` of an exception that cannot be thrown is a compile error.

### Blame and contracts

A definition's *contract* is the part that it promises to its callers: its inputs and outputs, its preconditions (`requires`), its postconditions (`ensures`), and its rejections.
A precondition binds the caller, and a postcondition binds the callee.
A violation names the side at fault, so that the reader knows which side to fix.

The table at the end lists, for each group, the command that reports it and the side at fault.

Precedent: Design by Contract in Eiffel (Meyer), where a broken precondition is the caller's error and a broken postcondition is the callee's error.

### Coverage

Every part of a spec is reached by some scenario or explored path.
A part that no run reaches has no evidence for its behavior.

`test`, with the coverage option, reports each part of the spec that no run reaches under `Uncovered`, so that you can add a scenario for it.

Precedent: statement and branch coverage in testing tools such as Istanbul and gcov.

## How to write a spec

The following principles shape the language itself.

### One explicit way

The language offers one way to write each meaning, and it requires you to write even the choice to do nothing, such as ignoring a rejection.
LLMs write tazuna specs, and one form per meaning removes variation and plausible omissions.

`check` reports a form that changes no meaning but is not the canonical one under `NonCanonical`.

Precedent: PEP 20, "There should be one-- and preferably only one --obvious way to do it" and "Explicit is better than implicit."

### Reject wrong forms early

tazuna rejects a wrong form with the earliest tool that can detect it, in this order: the TypeScript type checker, `check`, `test`, and `verify`.
A wrong form that an earlier tool reports is cheaper to fix.

This principle orders the checks of the other sections rather than adding one.

Precedent: Yaron Minsky's "make illegal states unrepresentable."

### Follow the standard

Where a standard defines a behavior, such as statecharts, request IDs, modal screens, or units, tazuna follows the standard's meaning.
Readers and implementers can then rely on what they already know.

Each definition that follows a standard names the standard in its doc comment, and no group reports a departure from a standard.

## Groups and what passing means

| Group | Reported by | Side at fault |
|---|---|---|
| `Malformed` | `check` | The spec. |
| `NonCanonical` | `check` | The spec. |
| `Restricted` | `check` | The spec. |
| `Illegal` | `check` | The spec. |
| `InvalidInput` | `test` | The scenario or the trace: an input that no caller or external service could give, including an external service that breaks the contract that the spec assumes of it. |
| `Fault` | `test` | The spec. |
| `OrderDependent` | `test` | The spec. |
| `ChoiceDependent` | `test` | The spec. |
| `Uncovered` | `test`, with the coverage option | The scenarios. |
| `Mismatch` | `verify`; `test` for its own snapshots | The implementation or external service whose trace differs, or the snapshot that differs from its scenario's run. |
| `Uncomparable` | `verify`; `test` for its own snapshots | The recorder or replay whose trace inputs differ from the scenario's, or the snapshot that has no scenario. |

A command passes when it reports none of its groups:

- When `check` passes, the spec type-checks, reads as written, and has no form that tazuna rejects.
- When `test` passes, `check` passes, every scenario and explored path runs without a violation and matches its snapshot, and, with the coverage option, every part of the spec is reached by some scenario or explored path.
- When `verify` passes, each implementation's traces match the snapshots, and each external service keeps the contract that the spec assumes of it.
