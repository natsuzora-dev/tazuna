# Writing specs

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
When more than one order can happen, state the order in the spec, or let a scenario line choose it.
The records of an entity have no order: spec functions receive them as a `Bag`, and its callbacks see one record at a time.
Find one record with `get(key)`, or with `filter(...).only()` when another field identifies it.
A result that needs an order goes through `sortedBy` with a number or time key, which groups the records with equal keys into runs that have no order inside.
A page of an ordered result takes whole runs, so it never cuts the records with equal keys apart.
`decide` returns the events for a `Bag` of records as one `Bag` of events.
Keep a callback from changing a variable outside it, through which it sees the order after all.

Precedent: CHESS, as in [guarantees.md](guarantees.md#ordering-and-determinism).

## Write a scenario as Given, When, and Then

This scenario is abridged from [samples/todo/spec/todo/scenarios.ts](../samples/todo/spec/todo/scenarios.ts):

```ts
export const completeTwice = scenario("Complete a task twice; todo rejects the second completeTask", {
  given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [], Settings: { shouldRemind: true } }, peers },
  when: (w) => {
    const add = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.net.deliver(add.request(calendar.nextBusinessDay));
    w.net.deliver(w.peer.calendar.answer(add.request(calendar.nextBusinessDay), day("2026-10-26")));
    const first = w.client.send(completeTask, { taskId: "task-1" });
    const second = w.client.send(completeTask, { taskId: "task-1" });
    return { first, second };
  },
  then: ({ first, second }) => [answered(first, accepted), answered(second, requires("notCompleted"))],
});
```

Write every record that a running service starts from: nothing defaults, and a single entity needs its record.
List in `peers` every service that the own service exchanges messages with, as `run(contract, records)`, `external(contract)`, or `skip(contract, because)`.
Key each by its service name; the types reject another key, the own service as a peer, and a line that names a message to a service that is neither the own service nor a running or external peer.
In Then, the types reject a `requested` request to a service that `peers` does not list and an `emitted` event of another service.
Repeat lines with a plain TypeScript function, such as a function that adds a task and delivers the calendar's answer.

Precedent: Given-When-Then (Behavior-Driven Development).

## Write every delivery

A message between two participants arrives only by a line that the scenario writes: `w.net.deliver(message)`, `redeliver`, `lose`, or `fail`, or `w.net.inFlight(message)` for a message that is still undelivered at the end.
An external peer answers only a request that reached it, and a request that reached it needs its answer or `leaveUnanswered`.
A message never overtakes an earlier one on its channel; to deliver the later one, lose or fail the earlier one first.
The clock line `w.clock.at(time)` names no order for deadlines of one service due at the same time: `test` fires them in every order and reports `ChoiceDependent` when the result differs, which the definition fixes, for example by guarding one transition on the other chart's state.
Two outcomes are the same when the records are equal and each channel carries the same messages in the same order; order across channels does not count, so two tied deadlines that each send a request differ in nothing, while two that each emit an event without `resultOf` differ in the order of the service's event channel.

Precedent: model checkers such as Stateright, which model the network as a set of messages that each step delivers.

## Refer to an earlier line through its handle

A line refers to a fact of an earlier line only through the handle that the line returned and the content it picks, never by a position or a count, because a count changes whenever a line is added before it.
When a handle matches more than one fact, pick by content, as in `add.request(calendar.nextBusinessDay, { input: { from: "2026-10-25" } })`.
When one processing sends equal requests, such as copies of a map state that ask `calendar.nextBusinessDay` with the same input, name them one by one with `requests`, as in `const [first, second] = add.requests(calendar.nextBusinessDay)`.
Nothing tells which request each handle names, so `test` runs every assignment and reports `ChoiceDependent` when one changes the result; requests that differ are `Report.ambiguousReference`, since a pick tells them apart.
Each request still needs its line, so a request that no handle names is `Report.leftInFlight`, and a handle beyond the requests sent is `Report.unresolvedReference`.
When the requests must be told apart, put an id in the input, such as the task's id, and pick by it.
Never write a key that a participant creates: read it through a handle, such as the `output` of the answer that holds it, and write `created()` in a running peer's message where its run creates the key.
Loading reports a value in the form of a created key (`<service>/<Entity>-<n>`) in Given or on a line as `Malformed.writtenCreatedKey`.
A spec does not compute such a string either: `test` compares runs up to a renaming of created keys, so the simulation reports one that no participant created as `Report.computedKey`.
Send a request again with `w.client.resend(line)`, and a new input under the id of an earlier line with `w.client.send(command, input, { sameIdAs: line })`.

Precedent: Hypothesis's stateful testing, whose rules refer to values that earlier rules made through named Bundles.

## Reach every part with a scenario

Write scenarios so that the run of some scenario reaches each part of the spec.
A part that no run reaches has no behavior that tazuna can compare.

## How tazuna is designed

### Reject wrong forms early

tazuna rejects a wrong form with the earliest tool that can detect it, in this order: the TypeScript type checker, `check`, the simulation of each scenario in `test`, the exploration in `test`, and `verify`.
A wrong form that an earlier tool reports is cheaper to fix.

Precedent: "make illegal states unrepresentable" (Yaron Minsky).

### Follow the standard

Where a standard defines a behavior, tazuna follows the standard: SCXML for statecharts, the `Idempotency-Key` header for request IDs, and WAI-ARIA for modal screens.
Readers and implementers can then rely on what they already know.
