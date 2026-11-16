# Writing specs

This page states the rules for writing a spec and the design of the language behind them.
The rules are not guarantees; [guarantees.md](guarantees.md) states what tazuna guarantees.

## Use the one canonical form for each meaning

The language offers one canonical way to write each meaning.
Write even the choice to do nothing explicitly, such as ignoring a rejection.
LLMs write tazuna specs, and a single form for each meaning leaves an LLM no variant to choose and no step to omit.
`check` reports a form that has a canonical alternative under `NonCanonical`.

Precedent: PEP 20, "There should be one-- and preferably only one --obvious way to do it" and "Explicit is better than implicit."

## Handle or ignore each declared rejection

Each command and query declares the rejections that it can return.
When you send a request that can be rejected, handle each rejection that it can return or explicitly ignore it.
A sender that cannot receive a rejection cannot write a handler for it.
The TypeScript type checker rejects the handlers that the types show to be unreachable, and `check` reports the remaining ones under `NonCanonical`.

Precedent: checked exceptions (Java).

## State every order that matters

A result must not depend on an order or a choice that nobody controls.
When more than one order can happen, state the order in the spec, or let an input choose it.
The records of an entity have no order: spec functions receive them as a `Bag`, and its callbacks see one record at a time.
Find one record with `get(key)`, or with `filter(...).only()` when another field identifies it.
A result that needs an order goes through `sortedBy` with a number or time key, which groups the records with equal keys into runs that have no order inside.
A page of an ordered result takes whole runs, so it never cuts the records with equal keys apart.
`decide` returns the events for a `Bag` of records as one `Bag` of events.
Keep a callback from changing a variable outside it, through which it sees the order after all.

Precedent: CHESS, as in [guarantees.md](guarantees.md#ordering-and-determinism).

## Refer to an earlier line by a name, not by a count

A scenario line refers to a fact of an earlier line only by a name that a line binds or by its content, never by a position or a count, because a count changes whenever a line is added before it.
createKey stands for a key that the implementation or its UI makes, such as a UUID, which no caller knows in advance.
When a later line uses a key that an input's processing creates, name the key on that input with `keys`, by entity and in creation order: after `send(addTitle, { title: "Buy bread" }, { keys: { Task: ["T-bread"] } })`, createKey returns `T-bread` for the first `Task` key that processing the input creates.
A key that a deadline or the service's begin creates while the time moves to an input's takes its name from the `at` line that moves it, as in `at("2026-10-25T10:00:00+09:00", { keys: { Note: ["N-hourly"] } })`, and a key that the reaction to a mock's answer creates from the mock's `keys`, as in `mock(planner, [calendar.nextDay, answer], { keys: { Task: ["T-next"] } })`.
`check` reports a name given twice to keys of one entity in one run (`Illegal.keyNamedTwice`), a value that a line has before the line that gives it as a name (`Illegal.keyUsedBeforeNamed`), and a value or name in the form of a counted key of the scenario's service or a peer, such as `Task-2` (`Illegal.countedKey`), which it looks for in every string field, a title too; `test` reports a name that createKey does not return while its line applies (`InvalidInput.unusedKeys`).
A mock chooses the request that it answers by content: `mock(planner, [calendar.nextDay, answer, { input: { from: "2026-10-25T11:00:00+09:00" } }])` answers the waiting request whose input has that `from`, whatever its other fields.
When the requests that a mock may answer have different inputs, `test` reports `InvalidInput.ambiguousMock` instead of choosing by the order of sending; of requests with equal inputs, which a trace cannot tell apart, the mock answers the longest-waiting.
An event names the mock whose request it results from, as in `receive(taskAdded, payload, { resultOf: added })`, and an unsubscribe names the subscribe input that opened its subscription, as in `const watching = subscribe(tasks, {})` and later `unsubscribe(watching)`; A line names only an input of its own run: the scenario's inputs to its service form one run, and a peer's given state with the scenario's `elsewhere` inputs to that peer another, and a subscription that a `from` line opens ends only by a `from` line of the same peer.
`check` reports a named input that the line's run takes more than once, or not before the line from the same sender (`Illegal.namedInputPlacedTwice`, `Illegal.namedInputUnplaced`), and checks the lines of a contract's state as those of a scenario named `states.<state>`.
Give an input an `id` only where the id itself is the point, such as an event delivered again or a command sent again.

Precedent: Hypothesis's stateful testing, whose rules refer to values that earlier rules made through named Bundles.

## Prepare the other services that a scenario mocks

`test` checks a scenario's mocks of another service of the spec against that service's run ([guarantees.md](guarantees.md#when-a-scenario-talks-to-another-service)), so write the inputs that the other service needs.
Write each start state of a service as inputs to it under `states` in its contract, with `keys` on the inputs whose keys the scenario uses, and name one per service in the scenario's `given`, such as `scenario(description, inputs, { given: { todo: todo.states.milkDueTomorrow } })`; a service that `given` does not name starts empty.
Write an input that the other service takes from someone else, such as the command whose event the scenario receives, as `elsewhere(todo, send(todo.addTask, input))` at its place among the scenario's inputs; the scenario's own service skips it.
Write a request that the other service sends to the scenario's service as `from(notifier, send(markSeen, input))` at its place among the scenario's inputs, naming the other service by its contract, which may be empty: the scenario's service takes it, `test` checks that the other service's run sends such a request by then, and that run gets the answers; a request of the other service that the scenario does not write gets no answer.
Repeat such inputs with a plain TypeScript function rather than a new option.
A mock may also name a key that the other service creates without a name with any string, one to one; `test` sends a later request with that string to the other service as its key.

## Reach every part with a scenario

Write scenarios so that the run of some scenario reaches each part of the spec.
A part that no run reaches has no behavior that tazuna can compare.

## How tazuna is designed

### Reject wrong forms early

tazuna rejects a wrong form with the earliest tool that can detect it, in this order: the TypeScript type checker, `check`, `test`, and `verify`.
A wrong form that an earlier tool reports is cheaper to fix.

Precedent: "make illegal states unrepresentable" (Yaron Minsky).

### Follow the standard

Where a standard defines a behavior, tazuna follows the standard: SCXML for statecharts, the `Idempotency-Key` header for request IDs, and WAI-ARIA for modal screens.
Readers and implementers can then rely on what they already know.
