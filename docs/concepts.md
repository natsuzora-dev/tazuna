# Concepts

[Guarantees](guarantees.md) defines the terms and states what each command proves.

## A spec is data that Lean runs

You write a spec in TypeScript, and tazuna turns it into data: the structure of each service, and each spec function as an expression tree, as LINQ turns a C# lambda into an expression tree.
Lean is the only place that gives this data a meaning.
The Lean engine runs it for `test`, `verify`, and `generate`, encodes it as SMT formulas for `prove` and `generate`, and reads the solver's answers back.
A Lean theorem proves that the encoding of each expression agrees with its evaluation, as Cedar proves its encoding against its evaluator.

With one meaning, no second interpreter can disagree with the definitions that the theorems are about.
TypeScript only types and translates the spec, and every answer of a command comes from Lean.

## tazuna owns only what it can run, encode, and prove

A construct belongs in the DSL only if Lean can run it, encode it exactly as SMT, and prove that encoding.
Everything else comes from outside the spec, from an external service or from the input.
That rule shapes the values a spec can hold:

- Numbers are integers. A spec holds an amount in its smallest unit, such as cents, as Cedar, TLA+, and Alloy do. `check` reports `z.number()` without `.int()` as `Restricted.schema`.
- An instant is milliseconds since the Unix epoch, within the range of a JavaScript `Date`, and a duration is milliseconds. A date is a `YYYY-MM-DD` label that a spec compares and adds days to. A spec converts neither between instants and dates nor between time zones. The ToDo sample asks its `calendar` service for the next business day instead.
- A spec builds no text for people. It sends a structured value, such as `{ id: "reminder", values: { title } }`, and the implementation renders it. `check` reports a template literal as `Restricted.function`.

`check` reports any code that the translation cannot turn into an expression as a `Restricted` kind, and the violation names the form to use instead.

## The spec decides every choice

No outcome may depend on an order that no line of the spec or scenario writes.
That makes the spec a test oracle: for the inputs of any log, the spec gives exactly one set of outputs, and `verify` can compare an implementation's outputs with it.
If tazuna resolved such a choice silently, the spec and an implementation could disagree for a reason that nobody wrote down.

Records have no order, because a database returns rows in an order that the spec does not control.
Spec functions receive the records of an entity as a `Bag`, and a spec that needs an order sorts by a key with `sortedBy`.
`minBy` and `maxBy` pick one record by a key, and a tie is `Fault.notOnly`, as `only` reports a bag with more than one value.

Some steps have no cause that orders them: two automations that react to one message, deadlines of one service due at the same time, and events or answers from other services that arrive at once.
Whether their order changes the outcome is a property of the whole spec, so `prove` checks it, not `test`: from any state within the bounds, it runs both orders to the end of each message and reports `ChoiceDependent.stepOrder` in a counterexample when the records, the lines written out, or whether the service halts differ.
`test` runs each scenario in one fixed order.
To fix the violation, make the definition order the steps, for example by guarding one transition on the state of the other chart.

Whether two orders give the same outcome depends on what each step changes:

- Two deadlines that each send one request give the same outcome, because the requests keep no order between them.
- Two deadlines that each write the same field with a different value do not, because the one that fires last decides the record.
- Two events that move one machine to different states do not, because the next event finds the machine in a different state.

## A scenario states the whole world

A scenario writes everything outside the services that it runs: the start time, the records, every request and operation, every move of the clock, every restart, and the fate of every message.
A message that no line delivers, loses, refuses, or leaves in flight is `InvalidScenario.leftInFlight`, not a message that arrives by default.

The run is deterministic, so a snapshot depends only on what the scenario wrote, and `test` can compare a run with it line by line.
`drive`, from `@natsuzora-dev/tazuna/verify`, puts the implementation in the same world: the same start, the same clock, and the same inputs in the same order.
If tazuna picked a delivery order or a default record, the implementation would face a world that nobody wrote down.

That world is the only control tazuna has over an implementation.
The implementation creates its keys and request ids in its own way, and `verify` binds them to the spec's values by where they first appear.

## The own service and its peers follow one set of rules

A scenario has one *own* service, whose behavior it states.
Every other service that the own service exchanges messages with is a peer, and Given lists each peer as running (`run`), external (`external`), or skipped (`skip`).
A skipped peer takes no part in the run: a message to it stays in its sender's trace and is then dropped, and no line may act for the peer.

Apart from what the role decides, the own service and its peers follow the same rules.
A message to or from the own service, a running peer, or an external peer arrives only by a line of the scenario, and a running peer's lines state the messages that its run sent.
That symmetry lets one scenario check both sides of an exchange.

tazuna checks an external peer's lines against its contract once, at the end of the scenario or trace, as a Pact provider verification replays its recorded interactions.
A result event may arrive before or after its request's answer, so a check in the middle of the exchange would read an incomplete record.

## A line names earlier messages through handles

Each line returns a *handle*, and a later line refers to what an earlier line caused only through that handle.
A handle names messages by their definition and, when needed, by their content, as a Playwright locator filters elements: `add.request(calendar.reserve, { day: "Mon" })`.
When nothing matches, or the matches differ, tazuna reports it instead of picking one.

A scenario never names a message by its position, such as "the second request that this command sent".
A command that sends one more request shifts every later position, and the scenario then names a different message without any error.
A handle that names content fails loudly instead.

A scenario also never writes a key that a running service creates with `createKey`.
The created key is the run's choice, and the implementation chooses differently, so the scenario reads the key through the handle of the line that returned it.

## Messages travel on channels

While a message is in flight, other lines can run.
That is how a scenario states a slow network, a lost answer, or a restart in the middle of an exchange.

Messages on one channel arrive in the order in which they were sent, as on one TCP connection or one Kafka partition, and nothing orders two channels.
The result events of a request travel on a channel of their own, as a Stripe webhook may arrive before the API response.
The spec orders two events on one channel only when one happens before the other, as in Lamport's happens-before.
Two steps that no cause chain links, such as the steps of two parallel regions, could run in two processes of a deployed system, so neither the snapshot nor `verify` records an order between their messages.
[Steps and channels](guarantees.md#steps-and-channels) gives the exact rules.

A message carries its value as the sender wrote it, and only the receiver parses it, as in a web API.
If the sender checked or normalized the value first, the spec would accept a message that the deployed receiver rejects.
A value fails its schema when it has a field that the schema does not name, at any depth, because a field that nothing reads is the writer's mistake.

A subscription lives as long as the process that serves it, as a WebSocket does, so a restart ends it.

## Every request names its caller

Each command and query lists its `callers`: entities whose records act as users, such as `User`, and services, such as `"notifier"`.
Spec functions read the `caller` beside the input, so a `requires` can let only a task's owner complete it.
A caller outside the list gets a `permission-denied` rejection, and a caller key with no record gets `not-found`.
A scenario states who sends each request, as in `w.client.as("screens").send(...)`.

The spec decides who may do what, and authentication stays outside it, as a Cedar policy reads a principal that something else signed in.
The list also tells `generate` which requests an outsider can send.

## A record is named by its key

An entity's `key` is one field, such as `key: "id"`, or a tuple of fields, such as `key: ["userId", "groupId"]`, whose value is an object of those fields.
A composite key states what makes a record unique, so a spec never builds an id from parts as text.

An input field of type `ref(E)` names a record, and spec functions read that record as `refs.<field>`, as Laravel binds a route parameter to its model.
A command that reads `refs.taskId` needs no lookup that may miss, and its rejection for a missing record is the service's `not-found`.

## Bounds set how far `prove` and `generate` look

Each service declares in `bounds()` how many records of each keyed entity a run may create, and how many items an array or `Bag` of an input, payload, or answer may hold.
`prove` proves each property for every state within the bounds, and `generate` searches inputs within them.
A small bound usually finds what a large one finds, as Alloy's small-scope hypothesis says, so start with two or three records per entity.
The bounds are typed by the entities that they name and reviewed with the spec, as TLA+ keeps its bounds in the model's configuration.

## Invariants and responses state what must hold

An invariant holds of a record, or of the whole service, in every state, and reads the record and `now`.
A response states a bounded promise: once `when` holds of a record and `expect` does not, `expect` must hold within `within` milliseconds, or the record must leave.
A missed response is `Fault.missedResponse` in `test` and `verify`.
A spec has no unbounded liveness, such as "eventually", because no finite run shows it broken.

## A counterexample is a decision about the spec

`prove` checks each invariant by induction.
It holds of the initial records, and it survives each step from any records within the bounds where every invariant holds.
The second part also starts from states that no run reaches, so a counterexample is one of two things:

- A real bug. Fix the behavior.
- A state that no run reaches. State the fact that rules it out as another invariant, or stop storing the value that can contradict another.

In the ToDo sample, without the invariant `createdBeforeNow`, `prove` reports a counterexample of `completedAfterCreated`: a task created after the current time, which `completeTask` then completes before its creation.
No run reaches that state, because `todo` creates each task at `now`.
The spec states that fact as `createdBeforeNow: record.createdAt <= now`, and both invariants are then proved.

tazuna never asks you for a fact about its own semantics, such as that the clock never moves back.
It assumes such facts, and [Assumptions](guarantees.md#assumptions) lists them.

## Every command writes structured output

`check`, `test`, `verify`, `prove`, and `generate` write one JSON line per result to stdout and a one-line summary to stderr, and `explain` writes one JSON line.
The usual reader is a program or a coding agent.
tazuna transforms a result only when a later step needs it, as `prove` decodes a solver's model to replay it in the semantics, and never only for readability: it does not shrink a counterexample.

## Each tool reports one kind of mistake

The TypeScript type checker reports a value of the wrong shape, such as a guard that reads a field that its state does not have.
`check` reports the rules that need the whole spec, such as whether the target of a request may reject, and every form that has a canonical alternative.
`test` reports what a scenario's run shows, `prove` what holds in every state within the bounds, and `verify` what an implementation's trace shows.
`generate` reports nothing wrong: it writes inputs that reach the parts no scenario reaches, for an implementation's tests to send.

Each rule lives in one tool.
The earlier tools report a mistake closer to the line that causes it, and they need no implementation.

Some violations point at the spec or the scenario even when nothing in them is wrong as written, because the run leaves open a choice that no comparison can settle.
`ChoiceDependent` and `Uncomparable.ambiguous` are such violations.
The fix writes the choice into the spec or the scenario, so that the spec and the implementation make it alike.

## Any log of the implementation can be checked

`verify` replays each trace in Lean: the spec takes the trace's `in` lines in order, and `verify` compares the trace's `out` lines with the spec's.
A trace can come from anywhere: `drive` running a scenario's snapshot or a generated input, or the implementation's own tests.
`verify --coverage` reports the parts of the spec that no trace reached, and `generate` writes inputs that reach most of them.

## Then states the intent, and the snapshot records the run

Then lists the facts that the scenario exists to check, and it does not have to list everything.
The snapshot records every message of the run, and `test` compares the run with it exactly, so a change in a message that Then leaves out still fails `test`.
Then is for a reviewer, and the snapshot is for `test`.

## Each meaning has one form

tazuna accepts one form for each meaning, and `check` reports a form that has a canonical alternative as `NonCanonical`.
The author of a spec is often an LLM.
Each variant that a language allows is a choice that the author makes without meaning to, and a reviewer then has to ask whether two forms mean the same thing.

For the same reason, a spec writes a choice to do nothing, such as `onRejected: []` for a rejection that it ignores on purpose.
An omitted handler would read the same whether the author decided to ignore the rejection or forgot it.

Data in a chart has one form per lifetime: `context` for what spans states, and `held` for one visit of a state, as a state carries its data in Erlang's gen_statem and in an Elm variant.
Because `held` stays fixed for the visit, a deadline's time and a guard of the state read the same value.
