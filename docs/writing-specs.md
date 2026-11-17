# Write specs

This guide shows how to lay out a spec and write its definitions and scenarios.
[Guarantees](guarantees.md) states what tazuna guarantees when a spec follows these rules.
Facts about one definition, such as the options of `command()`, are in its doc comment.

## Lay out the spec folder

`check`, `test`, and `verify` read every `.ts` file in the spec folder and its subfolders, except the files under `__snapshots__`.

- The `name` of a `service()` or `externalService()` call names the service.
  A definition belongs to the service whose definer made it, and a `constants()` call names its service as its first argument.
- A service or scenario name contains none of `.`, `/`, `#`, `@`, `[`, and `]` (`Malformed.reservedNameCharacter`).
- A file of one service imports only the contract of another service (`Restricted.crossServiceImport`).
- `test --update` writes the snapshots of a service's scenarios to `<service>/__snapshots__/` under the spec folder.

Folder and file names are free.
The samples keep one folder per service, named after it, and one file per kind of definition:

| File | Definitions |
|---|---|
| `data.ts` | Entities, the `service()` or `externalService()` call, and the `constants()` call |
| `events.ts` | Events |
| `commands.ts` | Commands |
| `queries.ts` | Queries |
| `automations.ts` | Automations |
| `machines.ts` | Machines |
| `<name>Screen.ts` | One screen of the `screens` service |
| `contract.ts` | The contract |
| `scenarios.ts` | Scenarios |

## Use the one form for each meaning

tazuna accepts one form for each meaning.
Write even the choice to do nothing, such as ignoring a rejection.
`check` reports a form that has a canonical alternative as `NonCanonical`.

## Handle or ignore each declared rejection

Each command and query declares the rejections that it can return.

- A state that `calls` or `sends` a request writes `onRejected` exactly when the answer can be rejected.
  To ignore the rejection, write `onRejected: []`.
- An automation writes `onRejected: []` exactly when its command can be rejected as `unavailable`.
  Any other rejection is a `Fault` of the automation.
- `check` reports a missing `onRejected` as `NonCanonical.missingOnRejected` and an unreachable one as `NonCanonical.unreachableOnRejected`.

## State every order that matters

A result must not depend on an order that nobody controls.

- Spec functions receive the records of an entity as a `Bag`, which has no order.
  Find one record with `get(key)`, or with `filter(...).only()` when another field identifies it.
- To order records, use `sortedBy` with a number, instant, or date key.
  It returns an array of runs.
  Records with equal keys form one run, which has no order inside.
  Slicing the array never splits a run.
- `decide` returns its events for a `Bag` of records as one `Bag` of events.
- Don't change a variable outside a callback.
  Through that variable, the result can depend on the order of the `Bag`.

## Write a scenario as Given, When, and Then

Write each scenario with the `scenario` definer of its service, the *own* service, and export it.
The export name is the scenario's name.
For a complete scenario, see [Test a first scenario](../README.md#test-a-first-scenario).

### Given

- `start` is the time at which every running service starts.
- `records` holds every record of the own service.
  Nothing defaults, so write the record of each single entity too.
- `peers` lists every service that the own service exchanges messages with, keyed by its service name:
  - `run(contract, records)` runs the peer's spec beside the own service.
    Each `w.peer.<name>` line states a message that the peer's run sent (`InvalidScenario.unpairedPeerLine`).
  - `external(contract)` makes the scenario write what the peer sends.
    The peer's contract checks those lines.
  - `skip(contract, because)` leaves the peer out and says why.

### When

Each call on `w` places one line and returns its *handle*.
The lines run in the order of the calls.

- `w.client` sends to the own service or to a running peer: `send`, `call`, `subscribe`, `unsubscribe`, and `resend`.
- `w.user` acts on a screen: `operate` uses a control, and `look` names the screen for Then's `offered` and `notOffered`.
- `w.peer.<name>` writes what a running or external peer sends: `answer`, `emit`, `send`, `call`, `subscribe`, and `unsubscribe`.
  `emit(event, payload, { resultOf })` names the command whose result the event is, or `null`.
  An external peer also has `leaveUnanswered`.
  A `w.peer` line puts its message in flight, and a `w.net` line delivers it.
- `w.net` decides the fate of a message in flight: `deliver`, `redeliver`, `lose`, `refuse`, and `leaveInFlight`.
- `w.clock.at(time)` moves the clock forward and fires the deadlines due by then.
- `w.host.restart()` restarts the own service.
- `w.startup` names what the startup of the running services caused, as a line's handle does.

To repeat lines, write a plain TypeScript function that takes `w`, such as a function that adds a task and delivers the calendar's answer.

### Then

Then returns what the own service did on the lines of When:

- `answered(line, answer)` for a request line, or `answered(line, [answers])` for a subscribe line.
- `emitted(line, [event(definition, payload)])` for the events that processing the line emitted.
- `requested(line, [request(definition, input)])` for the requests that it sent, with `subscription` and `endOf` for subscriptions.
- `offered(look, control)` and `notOffered(look, control)` for what a screen offers.

Then states only the facts that you want to check, and the snapshot records the rest.
`emitted` and `requested` compare their lists as bags.
The types reject a `requested` request to a service that `peers` does not list, and an `emitted` event of another service.

## Write the fate of every message

Every message to or from the own service, a running peer, or an external peer arrives only by a line of the scenario.
A message to a skipped peer is not delivered and needs no line.

- Deliver it with `w.net.deliver(message)`, deliver it again with `redeliver`, or drop it with `lose`.
- To make the sender get the transport's `unavailable` rejection, use `refuse(request)`.
- For a message that stays undelivered at the end, write `w.net.leaveInFlight(message)`.
- An external peer answers only a request that reached it.
  Write its answer, or `leaveUnanswered(request)`.
- A message never overtakes an earlier one on its channel.
  To deliver the later one, lose or refuse the earlier one first.

## Order the steps that change the result

`test` reports `ChoiceDependent.stepOrder` when two steps that no line orders give different results in their two orders.
The steps are deadlines of one service due at the same time, or steps of one processing that write what the other reads.
[Guarantees](guarantees.md#when-a-scenario-simulates) states which orders `test` runs and when two results are the same.

To fix the violation, make the definition order the steps, for example by guarding one transition on the state of the other chart.
Order across channels does not count.
Two tied deadlines whose only effect is to send one request each give the same result.
Two tied deadlines that each emit an event without `resultOf` to the same receiver do not, because the events share one channel.
Neither do two tied deadlines that each add a task that a subscription returns, because the answer after the first deadline shows which one fired first.

## Refer to an earlier line through its handle

A line refers to an earlier line only through that line's handle, never by position or count.

- A line's handle names what processing the line caused: `request(target, pick?)`, `requests(target, pick?)`, `subscription(query, pick?)`, `event(definition, { payload?, to? })`, `answer(requestLine)`, `end(subscription)`, and `screen(screen)`.
  Use `to` when an event has more than one receiver.
- When a handle matches more than one message, pick by content, as in `add.request(calendar.nextBusinessDay, { input: { from: "2026-10-25" } })`.
- When one processing sends equal requests, name them one by one with `requests`, as in `const [first, second] = add.requests(calendar.nextBusinessDay)`.
  Name every request.
  A request that no handle names is `InvalidScenario.leftInFlight`, and a handle beyond their number is `InvalidScenario.unresolvedReference`.
  `test` runs every assignment of the handles and reports `ChoiceDependent` when one changes the result.
  To tell the requests apart, put an id in the input and pick by it.
- Never write a key that a running service creates, of the form `<service>/<Entity>-<n>` (`Malformed.writtenCreatedKey`).
  Read it through a handle, such as the `output` of the answer that holds it.
  In a running peer's message, write `created()` where its run creates the key.
- Don't compute a string of that form in a spec function either (`InvalidScenario.computedKey`).
- To send a request again with the same id, use `w.client.resend(line)`.
  To send a new input under the id of an earlier line, use `w.client.send(command, input, { sameIdAs: line })`.
- To send an input that its schema rejects, wrap it in `raw(value)`.

## Reach every part with a scenario

Write scenarios so that some scenario's run reaches each part of the spec.
A part that no run reaches has no behavior to compare.
`test --coverage` reports such parts as `Uncovered`.
