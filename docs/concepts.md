# Concepts

[Guarantees](guarantees.md) defines the terms and states what a passing command proves.

## A scenario states the whole world

A scenario writes everything outside the services that it runs: the start time, the records, every request and operation, every move of the clock, every restart, and the fate of every message.
A message that no line delivers, loses, refuses, or leaves in flight is `InvalidScenario.leftInFlight`, not a message that arrives by default.

Two things depend on that.
The simulation is deterministic, so a snapshot depends only on what the scenario wrote, and `test` can compare a run with it line by line.
`drive`, which runs an implementation through a scenario from `@natsuzora-dev/tazuna/verify`, puts the implementation in the same world: the same start, the same clock, and the same inputs in the same order.
If tazuna picked a delivery order or a default record, the implementation would face a world that nobody wrote down, and a difference between the two runs would be nobody's fault.

That world is the only control tazuna has over an implementation.
The implementation creates its keys and request ids in its own way, and `verify` binds them to the simulation's values by where they first appear.

## The own service and its peers follow one set of rules

A scenario has one *own* service, whose behavior it states.
Every other service that the own service exchanges messages with is a peer, and Given lists each peer as running (`run`), external (`external`), or skipped (`skip`).

Apart from what the role decides, the own service and its peers follow the same rules.
A message to or from the own service, a running peer, or an external peer arrives only by a line of the scenario, and a running peer's lines state the messages that its run sent.
That symmetry lets one scenario check both sides of an exchange.
If the rule held only for the own service, a peer's message could arrive without a line, and the scenario would no longer state the whole world.

tazuna checks an external peer's lines against its contract once, at the end of the scenario or trace, as a Pact provider verification replays its recorded interactions.
A result event may arrive before or after its request's answer, so a check in the middle of the exchange would read an incomplete record.

## A line names earlier messages through handles

Each line returns a *handle*, and a later line refers to what an earlier line caused only through that handle.
A handle names messages by their definition and, when needed, by their content, as a Playwright locator filters elements: `add.request(calendar.reserve, { day: "Mon" })`.
It names every message that matches, and a line that uses it acts on each match in sending order.
When nothing matches, or the matches differ, tazuna reports it instead of picking one.

A scenario never names a message by its position, such as "the second request that this command sent".
A position breaks silently when the spec changes: a command that sends one more request shifts every later position, and the scenario then names a different message without any error.
A handle that names content fails loudly instead.
For the same reason, an operation names its screen instance by the handle of the line that opened it.

A scenario also never writes a key that a running service creates, such as `todo/Task-1`.
The created key is the run's choice, and the implementation chooses differently.
A scenario that wrote the simulation's key would state a fact about the simulation, not about the service, so it reads the key through the handle of the line that returned it.

## Messages travel on channels

While a message is in flight, other lines can run.
That is how a scenario states a slow network, a lost answer, or a restart in the middle of an exchange.

Messages on one channel arrive in the order in which they were sent, as on one TCP connection or one Kafka partition, and nothing orders two channels.
The result events of a request travel on a channel of their own, as a Stripe webhook may arrive before the API response.
The spec orders two events only along a cause chain, as Lamport's happens-before orders messages.
Two steps that no cause chain links, such as the steps of two parallel regions, could run in two processes of a deployed system, and nothing orders the messages of two processes.
Neither the snapshot nor `verify` records an order that a deployed system does not keep, so a spec cannot rely on one.
[Terms](guarantees.md#terms) gives the exact rules.

A message carries its value as the sender wrote it, and only the receiver parses it, as in a web API.
If the sender checked or normalized the value first, the simulation would accept a message that the deployed receiver rejects.
For the same reason, turning a parsed value back into JSON runs only its codecs and no check, as Pydantic and serde serialize a parsed value.
A value fails its schema when it has a field that the schema does not name, at any depth, as under JSON Schema's `additionalProperties: false`, because a field that nothing reads is the writer's mistake.
`verify` holds an implementation's lines to the same rule, so a field that the implementation writes beyond the spec is a `Mismatch`.

A subscription lives as long as the process that serves it, as a WebSocket does, so a restart ends it.

## No result depends on an order that nobody wrote

A choice that the scenario does not write and the spec does not make is an uncontrolled order.
The implementation resolves such a choice in its own way, so if tazuna resolved it silently, the simulation and the implementation could disagree for a reason that nobody wrote down.
tazuna removes some of these orders by construction and searches the rest.

Records have no order, because a database returns rows in an order that the spec does not control.
Spec functions receive the records of an entity as a `Bag`, and a spec that needs an order sorts by a key with `sortedBy`.
tazuna writes the elements of a bag, set, or `sortedBy` array in the order of their encoded values, which the trace holds, whatever a codec decodes them to.
For that reason `check` reports a `sortedBy` key whose encoded value is no number, instant, or date, and a union that holds a collection when one value can fit two of its options, since either would leave the order to a guess.

Some steps have no cause that orders them: deadlines of one service due at the same time (*tied* deadlines), the steps of one message that read and write the same data, and the events of one group that `decide` returns.
`test` runs all of these orders in one search and reports `ChoiceDependent.stepOrder` for the first order that gives a different outcome, as Concuerror, loom, and shuttle stop at the first failing schedule.
To fix the violation, make the definition order the steps, for example by guarding one transition on the state of the other chart.

Whether two orders give the same outcome depends on what each step changes.
The following examples show the difference:

- Two deadlines that each send one request give the same outcome, because the requests keep no order between them.
- Two deadlines that each emit an event without `resultOf` to the same receiver also give the same outcome, because the two steps have no send order.
- Two deadlines that each add a task that a subscription returns do not, because the answer after the first deadline shows which one fired first.
- Two events that move one machine to different states do not, even without a line, because the next event finds the machine in a different state.

The same search covers the messages that one line delivers to one service, equal messages included, since each has its own id.
For example, two copies of a map state that each reserve Monday for their task send equal requests, and a calendar that books the day for the first request it processes books a different task in each order.
The requests then need content that tells them apart, such as the task's id.

## Each meaning has one form

tazuna accepts one form for each meaning, and `check` reports a form that has a canonical alternative as `NonCanonical`.
The author of a spec is often an LLM.
Each variant that a language allows is a choice that the author makes without meaning to, and a reviewer then has to ask whether two forms mean the same thing.
With one form, two specs that look different mean different things.

For the same reason, a spec writes a choice to do nothing, such as `onRejected: []` for a rejection that it ignores on purpose.
An omitted handler would read the same whether the author decided to ignore the rejection or forgot it.

Data in a chart has one form per lifetime: `context` for what spans states, and `held` for one visit of a state, as a state carries its data in Erlang's gen_statem and in an Elm variant.
Because `held` stays fixed for the visit, a deadline's time and a guard of the state read the same value, and entering the state again is the only way to refresh it.
A value derived from records is a plain function that reads `records` where it is needed.

## The spec bounds what `test` explores

After each scenario, `test` explores every path of moves that the world enables, up to a depth, and each move writes its values from finite sets.
The spec declares both in `explore()`: the depth, and a `domain()` of values for each schema whose type is not finite, such as a string or a number.
A domain belongs to a schema, not to an input: it applies wherever the spec writes that schema, in every value that a move may carry.
Those values are the inputs of the service's commands and queries, and the outputs, events, and control payloads that a peer or a user writes, since any other service may be external in some scenario.
The bounds are typed by the schemas that they name and reviewed with the spec, as TLA+ keeps its bounds in the model's configuration, and `test` infers none of them.
For the same reason, a domain that names nothing, or two that name one schema, are mistakes that loading reports.
A small domain usually finds what a large one finds, so one or two values per schema is a good start.

## Then states the intent, and the snapshot records the run

Then lists the facts that the scenario exists to check, and it does not have to list everything.
The snapshot records every message of the run, and `test` compares the run with it exactly, so a change in a message that Then leaves out still fails `test`.
Then is for a reviewer, who reads it to see what the scenario is about, and the snapshot is for `test` and `verify`, which compare runs with it.

## Each tool reports one kind of mistake

The TypeScript type checker reports a value of the wrong shape or meaning, such as a guard that reads a field that its state does not have.
`check` reports the rules that need the whole spec, such as whether the target of a request may reject, and every form that has a canonical alternative, as Clippy does next to the Rust compiler.
`test` and `verify` report what only a run shows.

Each rule lives in one tool: the type checker, `check`, or `test` and `verify`.
A type sees one definition and the types it names, so a rule that also depended on the rest of the spec would be split between a type that covers some cases and `check`, which covers the others.
The earlier tools report a mistake closer to the line that causes it, and they need no implementation.

Some violations point at the spec or the scenario even when nothing in them is wrong as written, because the run leaves open a choice that no comparison can settle.
`ChoiceDependent` in `test` and `Uncomparable.ambiguous` in `verify` are such violations.
The fix writes the choice into the spec or the scenario, so that the simulation and the implementation make it alike.
