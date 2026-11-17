# Concepts

This page explains the ideas behind tazuna's specs and scenarios, and why tazuna works the way it does.
What each definer, actor, and violation kind does is in its doc comment.
What a passing command guarantees is in [Guarantees](guarantees.md).

## The scenario writes the whole world

A scenario controls everything outside the services that it runs: the start time, the records, every request and operation, every movement of the clock, every restart, and the fate of every message.
tazuna never fills in a part that the scenario leaves out.
A message that no line delivers, loses, refuses, or leaves in flight is `InvalidScenario.leftInFlight`, not a message that arrives by default.

tazuna works this way for two reasons.
First, the simulation is deterministic, so a snapshot depends only on what the scenario wrote, and `test` can compare it line by line.
Second, `drive` puts the implementation in the same world: the same start, the same clock, and the same inputs in the same order.
If tazuna chose a delivery order or a default record for the simulation, the implementation would face a world that the scenario never stated, and a difference between the two would be nobody's fault.

The implementation is controlled only through that world.
It creates its keys and request ids in its own way, and `verify` binds them to the simulation's values by where they first appear.
tazuna asks nothing else of how the implementation is written.

## Every service follows the same rules

A scenario has one *own* service, whose behavior it states.
Every other service that the own service exchanges messages with is a peer, which Given lists as running (`run`), external (`external`), or skipped (`skip`).

Apart from what the role decides, the own service and the peers follow one set of rules.
A message to or from the own service, a running peer, or an external peer arrives only by a line of the scenario.
A key that any running service creates is never written in the scenario.
A running peer's lines state the messages that its run sent, and its trace is a snapshot of its own, which `verify` compares with the peer's implementation in the same way as the own service's.

The symmetry is what lets one scenario check both sides of an exchange.
A rule that held only for the own service would let a peer's message arrive without a line, and the scenario would no longer state the whole world.

## A line refers to earlier lines through handles

Each line returns a *handle*, and a later line refers to what an earlier line caused only through that handle.
A handle names a message by its definition and, when needed, by its content.
When a handle matches no message or more than one, tazuna reports it instead of picking one.

A scenario never refers to a message by its position or by a count, such as "the second request that this command sent".
A position breaks silently when the spec changes: a command that sends one more request shifts every later position, and the scenario then names a different message without any error.
A handle that names content fails loudly instead.

A scenario also never writes a key that a running service creates, such as `todo/Task-1`.
The value of a created key is the run's decision, and the implementation makes it differently.
A scenario that wrote the simulation's value would state a fact about the simulation, not about the service.
The scenario reads a created key through the handle of the line that returned it.

## Messages travel on channels

A message stays *in flight* from the moment its sender sends it until a line of `w.net` decides its fate.
While a message is in flight, other lines can run, which is how a scenario states a slow network, a lost answer, or a restart in the middle of an exchange.

Messages on one channel keep their order, and messages on different channels keep none.
[Terms](guarantees.md#terms) defines which messages share a channel.
This model follows what a real transport promises.
One connection or one queue keeps its order, and nothing orders two connections.
A spec that relies on an order across channels relies on an order that a deployed system does not keep, so neither the snapshot nor `verify` records one.

## No result depends on an uncontrolled order

A choice that the scenario does not write and the spec does not make is an uncontrolled order.
tazuna does not resolve it silently, because the implementation would resolve it in its own way, and the simulation and the implementation would then disagree for a reason that nobody wrote down.
tazuna removes some of these orders by construction and searches the rest.

Records have no order.
Spec functions receive the records of an entity as a `Bag`, which has no index and no iterator, so a function cannot depend on the order in which a database returns rows.
To order records, the spec sorts them by a key with `sortedBy`, and records with equal keys stay one group without order.
A function can still depend on the order through a variable outside its callbacks, which `test` detects only partly as `BagOrderDependent`.

Some steps have no cause that orders them: deadlines of one service due at the same time, and the steps of one processing that read and write the same data.
`test` runs their orders and reports `ChoiceDependent.stepOrder` when two orders give different outcomes.
To fix the violation, make the definition order the steps, for example by guarding one transition on the state of the other chart.

Whether two orders give the same outcome depends on what each step changes, including the messages on each channel:

- Two tied deadlines that each send one request give the same outcome, because the two requests travel on different channels.
- Two tied deadlines that each emit an event without `resultOf` to the same receiver do not, because the two events share one channel.
- Two tied deadlines that each add a task that a subscription returns do not, because the answer after the first deadline shows which one fired first.

The same rule covers equal requests that one processing sends.
When a scenario names them one by one with `requests`, nothing decides which handle names which request, so `test` runs every assignment.
If an assignment changes the outcome, the requests need content that tells them apart, such as an id in the input.

## Each meaning has one form

tazuna accepts one form for each meaning, and `check` reports a form that has a canonical alternative as `NonCanonical`.
The author of a spec is often an LLM.
Each variant that a language allows is a choice that the author makes without meaning to, and a reviewer then has to ask whether two forms mean the same thing.
With one form, two specs that look different mean different things.

The same reasoning makes the spec write a choice to do nothing.
A state whose request can be rejected writes `onRejected`, and `onRejected: []` ignores the rejection on purpose.
An omitted handler would read the same whether the author decided to ignore the rejection or forgot it.

## Then states what you want checked

Then lists the facts that the scenario exists to check, and it does not have to list everything.
The snapshot records every message of the run, and `test` compares the run with it exactly, so a change in a message that Then leaves out still fails `test`.

The two parts have different readers.
Then is the scenario's intent, which a reviewer reads to see what the scenario is about.
The snapshot is the full record, which `test` and `verify` compare.

## Some violations are fixed in the spec or the scenario

Some violations point at the spec or the scenario even when nothing in them is wrong as written, because the run that they describe leaves a choice open that a comparison cannot settle.

`Uncomparable.ambiguous` is one.
`verify` binds each value that the snapshot creates, such as a request id, to the implementation's value.
When one processing sends equal requests that get different answers, the bindings can map an answer to either request, and the choice decides what the implementation receives next.
`verify` cannot tell which binding is right, so it reports the line.
To fix it, make the equal requests differ in content, or give them equal answers.

`ChoiceDependent` works the same way in `test`.
The spec is consistent, but its outcome depends on a choice that neither the scenario nor the spec makes.
The fix states that choice in the spec, so that the simulation and the implementation make it alike.
