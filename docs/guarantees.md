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
A trace can start with a line `{"type":"start","time","records"}`, which states the time and the records that the service starts from.

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
A *key position* is a value whose schema is `ref(E)`, `ref.self()` inside `E`'s own fields, or one of `E`'s key fields, such as `Task.fields.id`, at any depth of a message, a record, a context, or a map state's item key.
A *binding* pairs the values that one run created with the values of another run, one to one within each domain: the request ids, and the keys of each entity.
`test` and `verify` compare a string through the binding only at a key position, and compare any other string, such as a key held in a plain `z.string()`, as text.

### Bounds

A service's *bounds* are the numbers that its `bounds()` declares: `creates`, the most records of each keyed entity that a run creates, and `items`, the most items in each array or `Bag` of an input, payload, or answer.
A state is *within the bounds* when it holds at most `creates` records of each entity.
`prove` and `generate` write the bounds that they used on each result line.

### Violations

A *violation* is what a command reports.
Its kind, such as `Fault.failedEnsures`, names its *violation group* before the dot.
A run halts at a violation of a *halting* kind.
`tazuna explain <kind>` says whether a kind halts.

A run that halts gets none of the checks at the end of a run: the expectations of Then, the check of the messages left in flight, and the checks of the exchanges with external services.
The lines after the halt never took place, so those checks would read a cut-off record.
Only kinds of the groups `Fault`, `InvalidInput`, and `InvalidScenario` halt, as `halts` in `lean/Tazuna/Semantics/Service/Fault.lean`, `lean/Tazuna/Semantics/Service/InvalidInput.lean`, and `lean/Tazuna/Semantics/Sim/InvalidScenario.lean` decides.

## What a passing command means

A command *passes* when it reports no violation and `prove` reports no counterexample.
A command exits with 0 when it passes, with 1 when it reports a violation or a counterexample or tsc reports an error, with 3 when `prove` leaves a property undecided, and with 2 on a usage error.
`generate` exits with 0 whatever it finds.

- When `check` passes, every spec file type-checks under the nearest `tsconfig.json`, every spec function translates into an expression, and the spec has no violation of the groups that `check` reports.
- When `test` without `--only` passes, `check` passes, every line of every scenario takes place, every expectation of Then holds, and each running service's trace equals its snapshot.
  The scenario then states everything that happened between the running services, and each `InvalidScenario` kind is one rule of that statement.
- When `verify` passes, the spec takes every `in` line of every trace, and each trace [matches the spec](#when-a-trace-matches-the-spec).
  With `--coverage`, the replays also reach every part of the spec's commands, queries, automations, and charts.

When `verify` passes and the assumptions hold, the implementation sends the messages that the spec defines for the `in` lines of each trace.
tazuna guarantees nothing about inputs that no trace contains.

### What a `prove` verdict means

`prove` writes one verdict for each property of each spec service, within the service's bounds.

- `proved` means that the property holds in every state within the bounds that a run from the initial state reaches.
  For an invariant of records, `prove` shows that it holds of the initial records at any time, and after each command, with any input and caller at any time no earlier than the records' time, from any records within the bounds where every invariant holds and every record fits its schema.
  From the same records, it shows that each `ensures` holds and that no command leaves a ref that names a missing record.
  A chart's invariant holds when the chart starts and after each microstep, for any event, answer, or deadline in any configuration.
  For a pair of steps, deadlines, or arrivals, both [orders](#orders-that-prove-compares) end the same from any records and machine states within the bounds where every invariant, a machine's too, holds, and no machine is in a state that an always transition without a guard leaves at once.
- `counterexample` means that the semantics reports the violations that the line lists when it runs the command, query, or transition of the line from the line's state.
  `prove` replays every counterexample in the semantics before it reports it, and a replay that disagrees with the solver is an internal error, or undecided for a pair of deadlines or arrivals, whose chains leave out faults.
  The state may be one that no run reaches, as [A counterexample is a decision about the spec](concepts.md#a-counterexample-is-a-decision-about-the-spec) explains.
- `undecided` means that `prove` gives no verdict, for the reason that the line states, such as a construct that it does not encode or the solver's resource limit.

A spec holds no fractional numbers, since `check` reports them as `Restricted.schema`, so no verdict rests on floating-point arithmetic.

Some properties are undecided by design:

- A response is proved only when `when` implies `expect` in the initial records, after each command, and as time passes.
  A response that a deadline or a later step meets in time is undecided, unless the service has no automation and no chart, in which case `prove` reports a counterexample that states its progress assumption in `assumes`.
- A pair of deadlines or arrivals whose message can take more than 8 steps is undecided.
- A pair of deadlines or arrivals is undecided when its service has a screen, or a machine with parallel, final, history, or map states or with `held` data, or when its message runs an automation that creates a key, and so is an answer that several states or automations wait for.
- An invariant of a screen, or of a machine with parallel, final, history, or map states or with `held` data, is undecided.
- Each pair of steps whose order `prove` [does not compare yet](#orders-that-prove-compares) is undecided.

### What `generate` writes

`generate` writes one outcome for each part of each spec service that `verify --coverage` reports:

- `reached` names an input whose run in the semantics reaches the part, from no records at time 0.
- `unreachable` means that no state within the bounds lets the part's request reach the part, so no run within the bounds reaches it.
- `notReached` and `notEncodable` mean only that the search found no input. The part may still be reachable.

### Orders that `prove` compares

The spec decides every choice, so an outcome that depends on an order that no line writes is a violation.
`prove` compares, from any state where the invariants hold, both orders of:

- two automations that react to one event, or to two events that one command emits
- two deadlines of one service that can be due at the same time
- two messages from other services that can arrive at once: events that the service receives, and answers to requests that it waits for, each with its requesting state active

Each order runs each message to its end: the deadline's or event's transitions, the always transitions that follow, the own commands, the automations and machines that their events wake, and the activities of the states entered.
`prove` follows at most 8 steps of each message.
Two orders end the same when both halt, or when neither halts and both leave the same records and write the same out lines, in any order.
When they differ, `prove` reports `ChoiceDependent` in its counterexample.
When a message can take more than 8 steps, the pair is undecided.
`prove` does not compare yet the orders of the following pairs, and lists each pair that the spec can have as an undecided property:

- the events of one event group that one machine or automation takes (`groupOrder`)
- two own commands that states send in one round, and the answers to them (`roundOrder`)
- a deadline and a message from another service that arrives when it is due (`deadlineArrivalTie`)

`test` runs each scenario in one order: deadlines due at the same time fire in the order they were armed, the messages that one line delivers arrive in the order they were sent, and a message's queue takes its waiting steps in queue order.

### When a trace matches the spec

`verify` replays a trace: the spec takes the trace's `in` lines in order, each at its time, and writes its own `out` lines, with the [send order](#steps-and-channels) in their `after`.
A trace *matches* the spec when all of the following hold:

- The spec takes every `in` line of the trace.
- The `out` lines after each `in` line pair one to one with the spec's.
  In one pairing, each pair is equal under the binding and at an equal time, and the pairing keeps the order that each spec line's `after` names.
  `after` names only lines on one channel, and never two events at one time of one event group or of steps that no cause chain links.
  A trace line names no receiver, so `verify` takes the answers to one request, the events with one `resultOf`, and the events without `resultOf` each as one channel.
  For events, this channel is coarser than the spec's: events to different receivers share it, and `after` uses it too.
- One binding maps each value that the spec creates to one implementation value over the whole comparison.
  Paired lines have the same type, direction, name, and caller, and their contents, and the ids of `in` lines and outgoing requests, are equal under the binding.

An implementation that reuses an existing request id or key for a new one does not match.
An implementation that uses a string of its input, such as an idempotency key, as a new key can match.

`verify` keeps every binding that agrees with the lines compared so far.
The counts in a bag can decide a binding: the spec's `[K1, K1, K2]` against the implementation's `[x, y, y]` binds `K1` to `y`.
Keys that only a later line tells apart wait for that line.
When the bindings cannot decide what the implementation gets, or a trace cannot be compared at all, `verify` reports an `Uncomparable` kind.

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
A spec service's own resend stands for the request that it repeats, and an answer to the resend stands for an answer to that request, so the trace pairs with spec lines that sent the request once.

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
| `Fault` | `test`, `verify`, `prove` | The spec. |
| `RegionOrderDependent` | `test`, `verify` | The spec. |
| `ChoiceDependent` | `prove` | The spec. |
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
| `prove` | It proves each property for the states within the bounds. | States with more records of an entity than `creates`, and arrays and bags with more items than `items`. |
| `prove` | | Strings with a character after U+2FFFF, which Z3's strings cannot hold. |
| `Restricted` | It looks for the names of clocks, random sources, and locales in the spec files and in the local files that they import by a relative path. | A clock, random source, or locale that module code reaches by another name, or through a package that the spec imports. |
| `ChoiceDependent` | `prove` compares [both orders](#orders-that-prove-compares) of each pair from any state. | The pairs that `prove` lists as undecided: the orders that it does not compare yet, pairs in a service with a screen or a parallel, final, history or map state, and messages longer than 8 steps. |
| `ChoiceDependent` | | Faults inside a message, such as a failing invariant after a command, which other properties report. |
| `InvalidInput` | It checks an external peer's lines against the peer's contract. | A `requires` that reads more than the input, and an `ensures` that reads records. |

## Assumptions

tazuna detects a break of each assumption only in part or not at all.

- **Translation.** tazuna translates each spec function from TypeScript into an expression with the meaning that the TypeScript code has.
  No theorem covers the translation.
  The convert diff tests evaluate each operation and built-in of the expressions on random inputs in TypeScript and in Lean.
- **Types.** Each value in spec code has the type that the code declares.
  The translation picks each operation by the types of its operands.
- **Loading.** tazuna loads a spec in TypeScript, and no theorem states what loading guarantees of the structure that it builds.
  `check`'s `Malformed` and `Restricted` rules, and its `NonCanonical` rules that read the source, hold for that structure.
- **Scenario start.** Some theorems hold only for a scenario whose start meets their hypotheses, such as Given records with distinct keys.
  `test` checks Given before any line and reports `InvalidScenario.unlistedPeer`, `InvalidScenario.invalidRecord`, `InvalidScenario.duplicateRecord`, and `InvalidScenario.brokenGivenInvariant`.
  After any of them, no line runs.
  No theorem shows that a Given without these violations meets every hypothesis.
- **Message chains.** `prove` follows a message's steps in the queue order of the semantics, and replays each counterexample of an order pair in the semantics.
  No theorem proves that the chain it follows is the semantics' chain, so a pair it proves rests on that encoding.
- **Exchange checks.** The end-of-run checks of the exchanges with external services check what [Exchanges with external services](#exchanges-with-external-services) lists.
  No theorem ties each item of that list to the checks.
- **Cause chain.** The simulation computes the cause chain that [Steps and channels](#steps-and-channels) describes.
  The theorems under [Ordering](#ordering) state only the `after` that the computed cause chain gives.
- **Step encoding.** `prove` and `generate` encode each step, such as a command, a microstep of a chart, or the reactions of two automations, as SMT formulas over the encodings of its expressions.
  `seval_agrees` proves the encoding of expressions, and no theorem proves the encoding of steps.
  A counterexample and a `reached` input are replayed in the semantics, so they do not rest on this assumption.
  A `proved` verdict and an `unreachable` outcome do.
- **State facts.** `prove` assumes facts that every state of the semantics keeps: the clock never moves back, and each record and each chart's context fits its schema.
  The semantics checks a chart's context against its schema after each assignment, and no theorem proves that every state keeps these facts.
- **Adapter.** The `Adapter` through which `drive` drives the implementation controls the implementation's whole world.
  The implementation reads the time only from the clock that `advanceTo` moves, and receives messages only through the adapter.
  The adapter reports only the messages that the implementation received or sent, with the values that the implementation used.
  Its `settled` resolves only when the implementation has no work left that it can do before it gets a message or the clock moves.
  `drive` then gives the next `in` line, so an output that the implementation sends later is compared with the outputs of a later input, and does not match.
- **External services.** Each external service keeps the contract that the spec assumes of it.
  `test` and `verify` check only the [exchanges](#exchanges-with-external-services) that a scenario or a trace contains.
- **Opaque values.** An implementation treats the ids and keys that it did not create as opaque.
  Replacing them one to one in its inputs replaces them the same way in its outputs and changes nothing else.
  A running peer's implementation gets the values of other implementations, while the spec's replay holds the values of the spec, so `verify` assumes that the implementation behaves the same with either set of values.
- **Reproducible implementations.** Given the same world, an implementation sends the messages of its recorded trace.
  `verify` replays each implementation's trace on its own, so the claim that several implementations together produce the run that the spec gives rests on this assumption and the previous one.
- **Tools.** The Lean kernel, the Lean compiler that builds the engine, the TypeScript type checker, Node.js, and Z3 are correct, and so is the code that prints each query as SMT-LIB text.
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
| No two lines that a running service sends carry one id. The service names each line that it sends `<name>#<n>`, where `n` is one more than the number of its earlier lines of that name. | `sent_ids_distinct`, `start_sent_ids_distinct` |
| A message that a running service sends carries the id of its line, and a receiver judges ids per sender. | `post_message` |
| The `n`-th created key of an entity is `<owner>/<Entity>-<n>`, so no two createKey calls of one service return the same key. | `created_form`, `created_distinct` |
| In a run of a scenario, `createKey` of a keyed entity never returns a key that the scenario may write, such as a Given key. | `unwritten_not_created`, `execute_unwritten_not_created`, `start_unwritten_not_created` |
| The order in which Given writes the records does not matter. A scenario that writes the same records, no two with one key, in another order simulates alike. | `simulate_records_perm` |
| To find `RegionOrderDependent` violations, the semantics records what each chart function reads and assigns. The recording changes no step of a run: a service starts, processes each input, and checks the end of a run as it does without the recording. | `instrument_agrees`, `begin_agrees`, `send_agrees`, `call_agrees`, `subscribe_agrees`, `endSubscription_agrees`, `receive_agrees`, `answerIn_agrees`, `operate_agrees`, `fireDue_agrees`, `publish_agrees`, `restart_agrees`, `checkExchanges_agrees` |
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
| Two values that `test` or `verify` compares equal rename into each other under the binding that the comparison ends with: each key position as the binding pairs it, any other leaf equal, and bags and objects without repeated keys after reordering. | `matchValue_renamed` |

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
| A trace in which `verify` finds no violation matches the spec as [When a trace matches the spec](#when-a-trace-matches-the-spec) states. | `compare_matches`, `contentMatch_renamed` |
| When `check` reports no `Illegal` violation, the spec keeps the structural rule of each `Illegal` kind. | `check_eq_nil_iff` |
| When `check` reports none of the `NonCanonical` kinds that read only the structure, each transition has a `reenter` exactly when it leads within its source. | `canonical_check_eq_nil_iff` |
| When `check` reports none of the `NonCanonical` kinds that read only the structure, each automation and each calls or sends has `onRejected` exactly when an answer may be rejected. | `canonical_check_eq_nil_iff` |
| When `check` reports none of the `NonCanonical` kinds that read only the structure, no machine is stateless. | `canonical_check_eq_nil_iff` |

### Coverage

| Property | Theorems |
|---|---|
| `verify --coverage` reports only parts outside the reached parts that the replays collect. No theorem states that the collected parts are what the replays reached. | `uncovered_unreached` |

### Proof

| Property | Theorems |
|---|---|
| Under every assignment of the SMT variables, an expression that `prove` encodes throws exactly when its encoding's throw term holds, and otherwise has the value that its encoding gives. | `seval_agrees` |
| A date label of years 0000 through 9999 and its day number determine each other: parsing a label and rendering the day number give the label back, rendering a day number and parsing the label give the day number back, and a day number has a label exactly from 0000-01-01 through 9999-12-31. `prove` holds a date as its day number on these grounds. | `parse_render`, `render_parse`, `labelled_range` |
| The function that each `prove` query defines for the label of a day number means the label term of the encoding. | `dateLabelBody_denote` |
