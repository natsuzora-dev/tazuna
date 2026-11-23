# Guarantees

Lean definitions in [`lean/Tazuna`](https://github.com/natsuzora-dev/tazuna/tree/main/lean/Tazuna) of the tazuna repository state what a spec means, and Lean theorems prove properties of that meaning.
tazuna guarantees only what the theorems prove, under the [assumptions](#assumptions).
[Concepts](concepts.md) explains why the rules are what they are.

## Terms

### Traces and snapshots

A service interacts with the world only through messages.
It receives requests (commands, queries, and subscriptions), events, user operations on its screens, the current time, and restarts.
It sends answers, events, and requests of its own.
A service's *trace* is the sequence of these messages, each with its time.
An `in` line of a trace is a message that the service received, and an `out` line is a message that it sent.

The own service of a scenario and its running peers (`run`) are the *running services* of one *simulation*, and they share one clock.
A message to or from a running service stays *in flight* until a line of `w.net` decides its fate.
The simulation is deterministic.
A scenario's *snapshot* is the trace of its own service, and each running peer's trace is a snapshot of its own.

An `out` line of a snapshot can carry two fields that an implementation's trace does not:

- `after` lists the ids of the earlier `out` lines since the last `in` line that the [send order](#steps-and-channels) puts before this line.
- `created` lists the keys that `createKey` returned and that first appear, among the `out` lines, in this line.

### Steps and channels

A *step* is one unit of work in a service's queue: a chart that receives one event, a deadline that fires, an automation that reacts to one event, or a command that runs.
A service's *processing* of a line is the steps that the service takes for the messages that the line gives it.

Messages travel on *channels*, and the messages on one channel arrive in the order in which they were sent.
Messages on different channels keep no order.
A request and its end share the request's channel, and its answers travel back on a channel of their own.
The events that name one request as their `resultOf` travel on a channel of their own, so a result event may arrive before or after the request's answer.
An event without `resultOf` travels on the channel of its sender and receiver.

A command's `decide` returns an array of *event groups*.
An `emit(...)` in the array is a group of one event, and a `Bag` of `emit(...)` values is a group of its events.
The groups are in order, and the events of one group have no order.

The spec fixes the send order of the messages on one request's channel and of the answers to one request.
Of two events `a` and `b` on one channel, the spec sends `b` after `a` only in the following cases:

- `b` comes from `a`'s step, in a later event group of its `decide`.
- `b` comes from a step that `a`'s step caused, such as a machine's step that receives `a`.
  This chain of causes is the *cause chain*, and the step that enters a state causes the steps of that state's deadlines.
- `b` is sent at a later time than `a`, or while the service processes a later input.

Steps that no cause chain links, such as the steps of two parallel regions, two copies, or two deadlines due at the same time, have no send order.

### Charts

Machines and screens are statecharts, called *charts*.
A running chart is an *instance*.
A map state has one *map state copy*, or *copy*, of its child states for each key of its items.

### Keys and bindings

A *created key* is a key that `createKey` returned in a run.
A *key position* is a value whose schema is `ref(E)`, `ref.self()` inside `E`'s own fields, or `E`'s key field, such as `Task.fields.id`, at any depth of a message, a record, a context, or a map state's item key.
A *binding* pairs the values that one run created with the values of another run, one to one within each domain: the request ids, and the keys of each entity.
`test` and `verify` compare a string through the binding only at a key position, and compare any other string, such as a key held in a plain `z.string()`, as text.

### Explored paths

After each scenario, `test` explores paths of up to the `depth` that the service's `explore()` declares.
The `depth` counts moves, and `tazuna --help` says which network lines a move brings with it.
An *explored path* appends *moves* that the world enables:

- an external peer's answer to a request that the own service awaits and has not ended
- a clock line before or at the next deadline, and not before now
- an operation that an open screen accepts
- the end of a client subscription that no line ended
- a request to an own command or query
- an event of an external peer that the own service receives
- a restart

A move writes each value from the domains that `explore()` declares, or from its type when the type is finite.
A type is finite when it is a boolean, an enum, a literal, null, an object of finite types, or a union of them.
An optional field, or one with a default, may also be left out.
An answer is an output, a rejection of each kind that the target may give, or a `requires` rejection for each reason that the target lists.
Answers leave out `invalid-input` and `reused-id`, which blame the sender.
The own service checks the input of each request that it sends and gives it an id that none of its earlier requests carries, restarts included, so an honest peer never gives them.
An explored path uses new request ids and neither resends a command nor redelivers an event.

The *explored world* of a path is the simulation at the end of the path.
Its *fingerprint* is the part of it that `test` takes to decide what later paths report: the time, the messages in flight, and each running service's records, instances, deadlines, requests, subscriptions, and counts of line ids and created keys.
A fingerprint leaves out the trace and the violations reported so far.

### Violations

A *violation* is what a command reports.
Its kind, such as `Fault.failedEnsures`, names its *violation group* before the dot.
A run halts at a violation of a *halting* kind.
`tazuna explain <kind>` says whether a kind halts.

A run that halts gets none of the checks at the end of a run: the expectations of Then, the check of the messages left in flight, and the checks of the exchanges with external services.
The lines after the halt never took place, so those checks would read a cut-off record.
Only kinds of the groups `Fault`, `InvalidInput`, and `InvalidScenario` halt, as `halts` in `lean/Tazuna/Service/Fault.lean`, `lean/Tazuna/Service/InvalidInput.lean`, and `lean/Tazuna/Sim/InvalidScenario.lean` decides.

## What a passing command means

A command *passes* when it reports no violation.

- When `check` passes, every spec file type-checks under the nearest `tsconfig.json`, and the spec has no violation of the groups that `check` reports.
- When `test` without `--only` passes, `check` passes, every line of every scenario takes place, every expectation of Then holds, each running service's trace equals its snapshot, and no explored path reports a violation.
  The scenario then states everything that happened between the running services, and each `InvalidScenario` kind is one rule of that statement.
- When `test` and `verify` both pass with the same spec and snapshots, the trace that `drive` makes of the implementation in each scenario matches the snapshot.
  This holds for the own service and for each running peer that has an implementation.

When `test` and `verify` both pass and the assumptions hold, the implementation sends the messages that the spec defines for the lines of each scenario.
tazuna guarantees nothing about lines that no scenario contains.

### Step orders that `test` searches

`test` searches the orders that no line writes:

- the deadlines of one service due at the same time
- the messages that one line delivers to one service
- the steps of one message that no cause chain orders

A machine receives each event of an event group in a step of its own, so the order of an event group is one of these orders.
Each tied deadline, and each message of a line that delivers several, is ordered as one message with all its steps.
Two steps or messages conflict when what they read and write overlaps.
When `test` orders a whole message, what the message reads includes what the invariant checks and the subscription answers read after it.
`test` runs only the orders of conflicting ones.

`test` searches the step orders of each service's processing of each line separately, and each search stops at its first violation.
When an order changes the outcome, `test` reports `ChoiceDependent`.

Two outcomes are the same when both halt with the same violation, or when neither halts and both of the following hold:

- Their lines pair one to one with equal contents and the same `after` through the pairing.
  The lines that a service wrote for the messages of one line pair by message, as `verify` pairs `in` lines, and not by when the service processed them.
- The state that a later line reads is equal under one binding of created keys.
  That state is the records and each open instance and copy: the active states, the children that a history state returns to, the context, the `held` data of each active state, and the pending deadlines, whose times a later clock line reads.
  The binding maps each created key only to a key that the other run created for the same entity, and maps it alike at every key position: in records, contexts, `held` data, and map state item keys.

The open instances of one outcome pair with those of the other by name.
An instance that no screen opens is named by its chart, and a map state copy by its owner, its map state, and its item key under the binding.
A screen that another screen opens is named by its opener and by the state and key of that `opens`.
A screen that the same state opens again takes the name of the one it replaces, so neither the order in which screens open nor how many times a state opened its screen changes a name.

### When a trace matches a snapshot

A trace *matches* a snapshot when all of the following hold:

- Its `in` lines pair in order with the snapshot's `in` lines, at equal times.
- The `out` lines after each `in` line pair one to one with the snapshot's.
  In one pairing, each pair is equal under the binding and at an equal time, and the pairing keeps the order that each snapshot line's `after` names.
  `after` names only lines on one channel, and never two events at one time of one event group or of steps that no cause chain links.
  A trace line names no receiver, so `verify` takes the answers to one request, the events with one `resultOf`, and the events without `resultOf` each as one channel.
  For events, this channel is coarser than the spec's: events to different receivers share it, and the `after` of a snapshot uses it too.
- One binding maps each value that the snapshot creates to one implementation value over the whole comparison.
  Paired lines have the same type, direction, and name, and their contents, and the ids of `in` lines and outgoing requests, are equal under the binding.

An implementation that reuses an existing request id or key for a new one does not match.
An implementation that uses a string of its input, such as an idempotency key, as a new key can match.

`verify` keeps every binding that agrees with the lines compared so far.
The counts in a bag can decide a binding: the snapshot's `[K1, K1, K2]` against the implementation's `[x, y, y]` binds `K1` to `y`.
Keys that only a later line tells apart wait for that line.
When the bindings cannot decide what the implementation gets, or a trace cannot be compared at all, `verify` reports an `Uncomparable` kind.

`test` compares outcomes the same way, `after` included, so a spec without a `ChoiceDependent` violation fixes the `after` that `verify` checks.
An implementation's trace has no `after` or `created`, and `verify` reports a trace line that has either as `Uncomparable.lineSchema`.

### Exchanges with external services

`test` records every exchange with an external service and checks the following once, at the end of the scenario:

- the input that the service sent, against the external target's input schema, also when no answer came
- each answer, against the target's contract, also one that came after a restart
- a command's `ensures`, once an answer accepted the command, with all its result events
- each result event, against its request's answer

In the trace of an external service, an id names one request, as a Stripe `Idempotency-Key` does, since the answers and result events name requests by id.
A request line with an earlier line's id and the same type, name, and input, whatever the order of object fields, sends that request again, and each send gets at most one answer.
`verify` checks each answer to a send against the target's contract, and does not check that a resent request gets the first answer.
`verify` reports a line that reuses an id with another type, name, or input as `Uncomparable.duplicateId` and checks no later line, as it does for the requests that a spec service sends.
A spec service's own resend stands for the request that it repeats, and an answer to the resend stands for an answer to that request, so the trace pairs with a snapshot that sent the request once.

## Who fixes a violation

A definition's *contract* is what it promises: its inputs and outputs, its preconditions (`requires`), its postconditions (`ensures`), and its rejections.
The side that breaks a contract is at fault: the caller for a precondition, and the callee for a postcondition.

| Group | Reported by | Side at fault |
|---|---|---|
| `Malformed` | `check` | The spec. |
| `NonCanonical` | `check` | The spec. |
| `Restricted` | `check` | The spec. |
| `Illegal` | `check` | The spec. |
| `InvalidScenario` | `test`, `verify` | The scenario: a line that cannot take place, a message that it leaves unstated, or an expectation of Then that does not hold or cannot fail. For `verify`, the start line of the trace, whose records the spec rejects. |
| `InvalidInput` | `test`, `verify` | The scenario, or for `verify` the trace: a message that no sender could give the running service, including an external peer's answer that breaks the peer's contract. |
| `Fault` | `test`, `verify` | The spec. |
| `BagOrderDependent` | `test`, `verify` | The spec. |
| `ChoiceDependent` | `test`, `verify` | The spec. |
| `Undecided` | `test` | Neither side: the check stopped at a limit of tazuna. A smaller processing, or fewer created keys that only their keys tell apart, lets it decide. |
| `Uncovered` | `verify --coverage` | The tests that write the traces. |
| `Mismatch` | `test`, `verify` | The implementation or external service whose trace differs, or, for `test`, the snapshot that differs from its scenario's simulation. |
| `Uncomparable` | `test`, `verify` | The trace that the spec cannot replay or compare in one way, or an entry of the traces folder that is no trace, or, for `test`, a snapshot without a scenario or a scenario without a snapshot. |

## Detections

A *detection* is a check that can miss violations.
When a detection reports a violation, the violation is real.
When it reports nothing, the violation can still exist.
Each row below names one thing that a detection leaves out.

| Detection | How it detects | What it leaves out |
|---|---|---|
| Violations on explored paths | It runs every explored path. | Paths longer than the `depth` of `explore()`. |
| Violations on explored paths | | Values outside the declared domains. |
| Violations on explored paths | | Paths with an answer, an event, or a control payload whose parts each fit their domains but whose whole value fails a refinement of its schema. No one could write such a line, so `test` discards the path. A request with such a value stays, and the own service rejects it as `invalid-input`. |
| `Restricted` | It looks for the names of clocks, random sources, and locales in the spec files and in the local files that they import by a relative path. | A clock, random source, or locale that a spec function reaches by another name, or through a package that the spec imports. |
| `ChoiceDependent` | It searches the [step orders](#step-orders-that-test-searches) of each processing. | Orders beyond `Undecided.stepOrderLimit`. |
| `ChoiceDependent` | | The orders of a processing after its first violation. |
| `ChoiceDependent` | | The order of two steps that wait in the service's queue at once, are not message arrivals, and run the same definition on equal values, such as one automation's reactions to two equal events. The search names a step by what it runs and not by the step that caused it, so it takes such steps as one. |
| `ChoiceDependent` | | A difference in outputs that `verify` cannot compare, such as equal requests that get different answers. The state is still compared. |
| `ChoiceDependent` | | A state with too many bindings of created keys to compare, which it reports as `Undecided.stepOrderBindings`. |
| `ChoiceDependent` | | A screen's input, the answers to its `shows` requests, and the order of open screens, which the opener and the answer lines set. |
| `InvalidInput` | It checks an external peer's lines against the peer's contract. | A `requires` that reads more than the input, and an `ensures` that reads records. |
| `Uncovered` | It marks the parts that a scenario's run or an explored path reaches. | Parts that only paths longer than the `depth` of `explore()`, or values outside the declared domains, reach. |

## Assumptions

tazuna detects a break of each assumption only in part or not at all.

- **Runtime.** The TypeScript runtime that the commands run returns the same traces and violations as the Lean definitions.
  Diff tests compare the two only on tazuna's own example specs and traces, and for `test` on the paths of up to two moves after the example scenarios.
  They also check that `test`, which runs an explored path by continuing the run of the path one move shorter, gets the run that replaying every line gives.
- **Scenario start.** Some theorems hold only for a scenario whose start meets their hypotheses, such as Given records with distinct keys.
  `test` checks Given before any line and reports `InvalidScenario.unlistedPeer`, `InvalidScenario.invalidRecord`, `InvalidScenario.duplicateRecord`, and `InvalidScenario.brokenGivenInvariant`.
  After any of them, no line runs.
  No theorem shows that a Given without these violations meets every hypothesis.
- **Key order.** The TypeScript runtime gives spec functions the keys of an entity in one order, whatever order the records were written in, while the Lean definitions give the records in write order.
  No theorem covers this rule, and the two runtimes agree only when spec functions do not depend on the order of keys.
- **Loading.** tazuna loads a spec in TypeScript, and no theorem states what loading guarantees of the structure that it builds.
  `check`'s `Malformed` and `Restricted` rules, and its `NonCanonical` rules that read the source, hold for that structure.
  Loading also decides which schema a `domain()` names by Zod object identity, and no theorem covers that matching.
- **Step-order search.** The step-order search reaches every order of conflicting steps that changes a message's outcome.
  No theorem proves it, and a proof needs two facts: steps that do not conflict give the same outcome in either order, and the conflict check sees every read and write of every step.
- **Exchange checks.** The end-of-run checks of the exchanges with external services check what [Exchanges with external services](#exchanges-with-external-services) lists.
  No theorem ties each item of that list to the checks.
- **Cause chain.** The simulation computes the cause chain that [Steps and channels](#steps-and-channels) describes.
  The theorems under [Ordering](#ordering) state only the `after` that the computed cause chain gives.
- **Fingerprints.** Two explored worlds with the same fingerprint report alike on every later path of the same number of moves: what the first reports, the second reports too, or its own path reported already.
  A path reports the violations that it adds and the parts that it reaches first.
  `test` extends only the first explored world of each fingerprint, so its explored paths rest on this assumption.
  No theorem proves it, and the diff test of explored paths checks only that the TypeScript runtime and Lean take the same worlds as the same.
- **Fingerprint hashes.** `test` keeps a 64-bit hash of each fingerprint instead of its text, so two worlds whose fingerprints share a hash also count as one.
  It writes the probability of that, as TLC does, when the probability is at least 1e-12.
- **Spec functions.** Spec functions are deterministic.
  They read no clock, random source, or mutable global state, and they receive the current time as an argument.
  A result of a spec function depends neither on the order in which a `Bag` visits its values nor on the order of keys, as a comparison such as `a.id < b.id` would.
- **Types.** Each value in spec code has the type that the code declares.
- **Adapter.** The `Adapter` through which `drive` drives the implementation controls the implementation's whole world.
  The implementation reads the time only from the clock that `advanceTo` moves, and receives messages only through the adapter.
  The adapter reports only the messages that the implementation received or sent, with the values that the implementation used.
  Its `settled` resolves only when the implementation has no work left that it can do before it gets a message or the clock moves.
  `drive` then gives the next `in` line, so an output that the implementation sends later is compared with the outputs of a later input, and does not match.
- **External services.** Each external service keeps the contract that the spec assumes of it.
  `test` and `verify` check only the [exchanges](#exchanges-with-external-services) that a scenario or a trace contains.
- **Opaque values.** An implementation treats the ids and keys that it did not create as opaque.
  Replacing them one to one in its inputs replaces them the same way in its outputs and changes nothing else.
  A running peer's implementation gets the values of other implementations, while its snapshot holds the values of the simulation, so `verify` assumes that the implementation behaves the same with either set of values.
- **Reproducible implementations.** Given the same world, an implementation sends the messages of its recorded trace.
  `verify` compares each implementation's trace with its own snapshot, so the claim that several implementations together produce the simulated run rests on this assumption and the previous one.
- **Tools.** The Lean kernel, the TypeScript type checker, and Node.js are correct.
  The Lean build fails on `sorry` and on any axiom other than `propext`, `Classical.choice`, and `Quot.sound`, so no theorem rests on an unproven step.

## Proven properties

Each property holds for every spec, and the theorems in `lean/Tazuna/Thm` prove it.

### Simulation

| Property | Theorems |
|---|---|
| Then only adds violations. A scenario leaves the same traces, messages, and halt as the same scenario without Then, so a snapshot depends on Given and When alone. | `then_only_reports` |
| The checks at the end of a run only add violations. | `simulate_reported` |
| A line that is not a deliver, lose, or refuse line leaves every message in flight as it is. | `line_keeps_leftInFlight` |
| A deliver, lose, or refuse line leaves every message in flight as it is, except those that its handle names. | `moving_line_keeps_others` |
| Only a line that gives a running service something to process changes its state: a client's request, end, or resend, an operation, a clock or restart line, or a deliver, redeliver, or refuse line. | `line_keeps_states` |
| A deliver line halts the simulation and delivers nothing when an earlier message that the line does not name is still in flight and must arrive before one of the line's messages. An earlier message must arrive first when it travels on the same channel and, for two events of a running service, the [send order](#steps-and-channels) puts it first. | `overtaking_delivery_halts` |
| An external peer's answer line that names a request that has not reached the peer halts the simulation. | `external_answer_needs_delivery` |
| A halting `InvalidScenario` violation halts the simulation. | `halting_report_stops` |
| Once the simulation halts, the steps of the later lines take no effect. | `lines_after_stop_ignored` |
| A halting `Fault` or `InvalidInput` of a running service halts the simulation. | `halting_finding_stops` |
| A run that halts gets no checks of the exchanges with external services. | `stopped_run_skips_exchanges` |
| A refuse line that names one request in flight loses the request and delivers the `unavailable` answer to its sender. | `refuse_answers_unavailable` |
| Each line keeps every created key. | `execute_keepsKeys`, `created_kept` |
| Each line keeps the earlier lines of every running service, restarts included. | `sent_ids_distinct` |
| No two lines that a running service sends carry one id, whatever step orders the step-order search sets. The service names each line that it sends `<name>#<n>`, where `n` is one more than the number of its earlier lines of that name. | `sent_ids_distinct`, `start_sent_ids_distinct` |
| A message that a running service sends carries the id of its line, and a receiver judges ids per sender. | `post_message` |
| The `n`-th created key of an entity is `<owner>/<Entity>-<n>`, so no two createKey calls of one service return the same key. | `created_form`, `created_distinct` |
| In a run of a scenario, `createKey` of a keyed entity never returns a key that the scenario may write, such as a Given key. | `unwritten_not_created`, `execute_unwritten_not_created`, `start_unwritten_not_created` |
| The order in which Given writes the records does not matter. A scenario that writes the same records, no two with one key, in another order simulates alike. | `simulate_records_perm` |
| To find `BagOrderDependent` and `ChoiceDependent` violations, `test` records what each spec function reads and writes. The recording changes no step of a run: a service starts, processes each input, and checks the end of a run as it does without the recording. | `instrument_agrees`, `begin_agrees`, `send_agrees`, `call_agrees`, `subscribe_agrees`, `endSubscription_agrees`, `receive_agrees`, `answerIn_agrees`, `operate_agrees`, `fireDue_agrees`, `publish_agrees`, `restart_agrees`, `checkExchanges_agrees` |
| A run of a whole scenario with the recording leaves the world that the run without it leaves, whatever the recording collected before. | `execute_agrees`, `simulate_agrees` |

### Data validity

| Property | Theorems |
|---|---|
| An accepted command emits exactly the events that its `decide` returned, each once, in the event groups that `decide` returned. | `accepted_emits_decided` |
| Every emitted event is one that `emits` lists, and an unlisted event halts the run. | `accepted_emits_decided`, `unlisted_emitted_event_halts` |
| Each emitted payload has its collections sorted by the declared schema, is parsed by it, and is sorted again, since parsing fills defaults as the schema writes them. | `decide_payloads_sorted`, `instrument_agrees` |
| The service answers a query with the output of its `resolve`, its collections sorted by the declared schema, parsed by it, and sorted again. | `resolve_output_answered`, `sorting_resolve_parsed`, `instrument_agrees`, `requirements_lookup` |
| When the input of a command or query does not fit its schema, the service rejects it with `invalid-input`. | `command_invalid_input_rejected`, `query_invalid_input_rejected` |
| A spec service's `invalid-input` answer to another spec service is the sender's `Fault`. | `invalid_input_answer_blames_sender` |

### Statecharts

Charts follow the SCXML (W3C) algorithm in the first six rows.
The other rows are tazuna's own.

| Property | Theorems |
|---|---|
| A chart enters its initial states. | `enters_initial` |
| A microstep exits descendants before ancestors. | `microstep_exits_in_exit_order`, `exitOrder_descendants_first` |
| A microstep enters ancestors before descendants. | `microstep_enters_in_entry_order`, `entryOrder_ancestors_first` |
| A chart takes only transitions that active leaves pick, in leaf order. A leaf picks a transition of its innermost state that takes the event. | `select_follows_leaves`, `select_picked_by_leaf`, `leaf_selects_innermost` |
| A transition to an ancestor exits it. | `ancestor_target_exits` |
| An operation that no transition takes changes nothing. | `untaken_operation_changes_nothing` |
| A transition to a descendant of its source exits the source when it reenters, and keeps it otherwise. | `reenter_true_exits`, `reenter_false_not_exited` |
| A stopped instance processes no event. | `stopped_machine_takes_no_event` |
| An event whose payload lacks a key field of a map state reaches every copy of that map state. | `keyless_payload_reaches_all` |
| An event whose payload has every key field of a map state reaches at most one copy of it, when the copies have distinct keys. | `keyed_payload_reaches_at_most_one` |

### Requests and deadlines of a state

| Property | Theorems |
|---|---|
| A deadline fires only while its state is active. | `fires_only_in_active_state` |
| Leaving a state makes its awaited requests and queued commands stale. | `leave_makes_requests_stale`, `leave_makes_queued_stale` |
| An answer to a stale request only ends the wait for it. | `stale_answer_ignored`, `stale_command_answer_ignored` |
| A state that is exited before it sends its requests sends nothing. | `exited_state_sends_nothing` |
| When every deadline and live request of an instance belongs to one of its active states, stopping the instance cancels them all. | `endWith_cancels_deadlines_and_requests` |
| In a spec that `check` accepts, every deadline with a delay has a length in milliseconds that the run adds to the time its state is entered. | `deadlines_exact` |

### Subscriptions and screens

| Property | Theorems |
|---|---|
| When the service publishes, it sends a new answer to a subscription only when the answer changes. | `changed_answer_sent`, `unchanged_answer_not_sent` |
| Publishing sends no answer to a subscription id that no open subscription has. | `ended_subscription_not_answered` |
| Opening a screen creates one child instance of the opened screen. | `entering_opens_one_child`, `requirements_lookup` |
| Among the screens open above an operated screen, a modal one covers it, as in the WAI-ARIA modal dialog. | `modal_child_covers` |
| Non-modal screens above an operated screen leave it operable, so several open instances of one screen are each operable. | `nonmodal_child_lets_parent` |

### Time

| Property | Theorems |
|---|---|
| The steps of a message never change the current time. | `drain_keeps_now` |
| Every line that the steps of a message and the checks after them write carries the current time. | `message_outputs_at_its_time` |
| A deadline due by the time that the clock moves to fires as a message of its own, at its time. | `deadline_message_at_its_time` |
| Deadlines of one service due at the same time fire in the step order that `test` searches, whichever line moved the time. | `chooseDeadline_stepOrder` |
| Only a clock line moves the current time of a running service, which every line that the service writes carries. | `only_clock_moves_time` |
| A clock line publishes the subscription answers that the new time changes. | `clock_publishes` |

### Processing and completion

| Property | Theorems |
|---|---|
| A command is processed as one message, with the work that it causes. | `command_one_message` |
| Processing that still has work when it reaches a limit that tazuna sets halts with the `Fault` of that limit. | `always_rounds_limit_halts`, `command_limit_halts`, `done_selections_limit_halts`, `due_deadlines_limit_halts`, `message_work_limit_halts` |
| A failed postcondition or invariant is a `Fault` of the command after which it fails. | `failed_ensures_blames_command`, `entity_invariant_reported_iff`, `service_invariant_reported_iff` |
| A rejected command writes no record and emits no event. | `rejected_command_changes_nothing` |
| An accepted command leaves exactly the records that applying its emitted events gives. | `accepted_command_writes_then_queues_reactions` |

### Ordering

| Property | Theorems |
|---|---|
| The elements of a bag or set, and the elements with equal keys in an array sorted by a key, are in the order of the canonical JSON of their encoded values. | `bag_or_set_array_sorted`, `sortByKey_equal_keys_in_canonical_order` |
| The elements of a bag or set sort to the same canonical JSON in whatever order spec code built them. | `sortCanonical_perm` |
| The elements of a `sortedBy` array sort to the same list in whatever order spec code built them, when no two distinct elements have the same canonical JSON. No theorem shows that only values that differ in field order do. | `sortByKey_perm` |
| In a union that holds a collection and that `check` accepts, a value fits at most one option, so the option that sorts it is never a guess. | `apart_disjoint` |
| A snapshot orders two `out` lines after one `in` line only when they travel on one channel. | `ordered_same_channel` |
| A snapshot never orders two events at one time of one event group. | `group_lines_unordered` |
| A snapshot never orders two events at one time of steps that no cause chain links. | `independent_unordered` |

### Identity

Request ids follow the `Idempotency-Key` HTTP header (IETF).
The last four rows of the table state renamings under conditions on the binding.
They apply to the binding that `test` or `verify` ends with only when that binding pairs only keys and request ids, and pairs each key with a key of its own entity.
No theorem shows that it does.

| Property | Theorems |
|---|---|
| Each input keeps the keys of a keyed entity distinct. | `send_keysDistinct`, `message_keysDistinct` |
| A reference that does not resolve is a `Fault`. | `dangling_ref_reported_iff` |
| When a command arrives again with the same id and the same input, the service answers it with the first answer and does not run it again. | `resent_command_gets_first_answer` |
| The service rejects a command that reuses an id with another input, whatever the order of object fields. | `reused_id_rejected` |
| The service answers a repeated query again, because a query has no identity. | `query_answered_again` |
| When an event or an answer arrives again with the same id, the service does not process it again. | `redelivered_event_not_processed`, `redelivered_answer_not_processed` |
| Two values that `test` or `verify` compares equal rename into each other under the binding that the comparison ends with: each key position as the binding pairs it, any other leaf equal, and bags and objects without repeated keys after reordering. | `matchValue_renamed`, `sameState_renamed` |
| For a binding that pairs only keys and request ids, that renaming is a renaming in the sense of the next three rows. | `matchValue_strRenamed` |
| Every value renames to itself. | `renamed_refl` |
| A renaming read backward is the inverse binding, when each binding pairs each key with a key of its own entity. | `renamed_symm` |
| Two renamings in a row are their composition, which is again one to one, when each binding pairs each key with a key of its own entity. | `renamed_trans`, `compose_fst_nodup`, `compose_snd_nodup` |

### Restart

| Property | Theorems |
|---|---|
| A restart begins the service again from the part of its state that it persists: its records, its command answers, the events and answers that arrived, and its created keys. It discards the part in its process memory: its instances, deadlines, awaited requests, and subscriptions. | `restart_keeps` |
| An answer that arrives when its request waits no more, as after a restart, is written and has no other effect. The end of the run checks it with the other answers, and no theorem states that check. | `late_answer_written` |
| A restart reads nothing of the state that it discards. | `restart_forgets` |
| A restart ends every subscription for `verify`, which compares the lines after it as if no subscription were open and keeps the first answer of a subscription that opens again. | `first_answer_after_restart_kept` |

### Comparison

| Property | Theorems |
|---|---|
| A snapshot matches a run when their lines have equal canonical JSON, whatever the order of object fields. | `compareSnapshot_eq_none_iff`, `compareSnapshot_reordered` |
| A trace in which `verify` finds no violation matches its snapshot as [When a trace matches a snapshot](#when-a-trace-matches-a-snapshot) states. | `compare_matches`, `contentMatch_renamed` |
| When `check` reports no `Illegal` violation, the spec keeps the structural rule of each `Illegal` kind. | `check_eq_nil_iff` |
| When `check` reports none of the `NonCanonical` kinds that read only the structure, each transition has a `reenter` exactly when it leads within its source. | `canonical_check_eq_nil_iff` |
| When `check` reports none of the `NonCanonical` kinds that read only the structure, each automation and each calls or sends has `onRejected` exactly when an answer may be rejected. | `canonical_check_eq_nil_iff` |
| When `check` reports none of the `NonCanonical` kinds that read only the structure, no machine is stateless. | `canonical_check_eq_nil_iff` |
| When the step-order search of a message reports nothing, each order that it ran either could not run, because no queue takes the steps in that order, or gives the same outcome as the execution that it came from. | `stepOrderSearch_same` |
| The step-order search does not swap two steps of which one is an `always` round of an instance that the other settles around: either order gives the same processing. | `always_step_independent` |
| The same outcome means the same halt, or outputs that pair through one pairing with the same `after` and a state equal under a binding of created keys, as [Step orders that `test` searches](#step-orders-that-test-searches) defines. When `verify` cannot compare the first execution's outputs even with themselves, as the `ChoiceDependent` rows of [Detections](#detections) say, the same outcome means only a state equal under a binding. | `difference_same`, `compareTraces_ok`, `sameState_renamed` |

### Exploration

| Property | Theorems |
|---|---|
| `verify --coverage` reports only parts outside the reached parts that the replays collect. No theorem states that the collected parts are what the replays reached. | `uncovered_unreached` |
