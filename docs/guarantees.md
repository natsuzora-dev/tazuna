# Guarantees

Lean definitions in [`lean/Tazuna`](../lean/Tazuna) state what a spec means, and Lean theorems prove properties of that meaning.
tazuna guarantees only what the theorems prove, under the [assumptions](#assumptions) below.
[Write specs](writing-specs.md) shows how to write the specs and scenarios that this page refers to.

## Terms

A service interacts with the world only through messages.
It receives requests (commands, queries, and subscriptions), events, user operations on its screens, the current time, and restarts.
It sends answers, events, and requests of its own.
The sequence of these messages, each with its time, is the service's *trace*.

A scenario's own service and its running peers (`run`) are the *running services* of one *simulation*.
They share one clock.
A message between two of them stays *in flight* until a line of `w.net` decides its fate.
The simulation is deterministic: the scenario writes every choice that no service's code makes, such as which message arrives next and when the time advances.

Messages travel on *channels*.
A request, its answers, its end, and the events that name it as their `resultOf` share the request's channel.
An event without `resultOf` travels on the channel of its sender and receiver.
Messages on one channel keep their order, and messages on different channels keep none.

The trace of the own service in a scenario is the scenario's *snapshot*, and the trace of each running peer is a snapshot of its own.

A *violation* is what a command reports.
Each violation has a kind, such as `Fault.failedEnsures`, and the part before the dot is its *group*.
The doc comment of a kind states what it means.
A run stops at a violation of a *halting* kind, because the behavior after it is undefined.
`halts` in `lean/Tazuna/Service/InvalidInput.lean` and `lean/Tazuna/Sim/InvalidScenario.lean` defines which kinds halt.

## What a passing command means

A command *passes* when it reports no violation.
tazuna reports each mistake with the earliest tool that can detect it, in this order: the TypeScript type checker, `check`, the simulation in `test`, the exploration in `test`, and `verify`.

- When `check` passes, the spec type-checks and has no violation of the groups that `check` reports.
- When `test` passes, `check` passes, every line of every scenario takes place, every expectation of Then holds, and each running service's trace equals its snapshot.
- When `test` and `verify` both pass with the same spec and snapshots, the trace that `drive` makes of the implementation in each scenario matches the snapshot.
  This holds for the own service and for each running peer that has an implementation.

When the assumptions also hold, the implementation sends the messages that the spec defines for the lines of each scenario.
tazuna guarantees nothing about lines that no scenario contains.

### When a scenario simulates

When `test` reports no `InvalidScenario` violation, the scenario states everything that happened between the running services:

- Every message between two running services reached its receiver by a line, or the scenario names it as lost, refused, or left in flight (`InvalidScenario.leftInFlight`).
- No message overtook an earlier one on its channel (`InvalidScenario.overtaking`).
- Each line of a running peer states a message that its run sent.
- Each answer of an external peer answers a request that reached it, and each such request is answered or left unanswered, not both (`InvalidScenario.awaitingAnswer`, `InvalidScenario.repeatedAnswer`).
- An event's `resultOf` names a request that its emitter received (`InvalidScenario.unreceivedRequest`).
- Each handle named one message, and the handles of `requests` named equal requests (`InvalidScenario.unresolvedReference`, `InvalidScenario.ambiguousReference`).
- The clock only moved forward (`InvalidScenario.notLater`).
- The scenario wrote no key that a running service creates (`InvalidScenario.writtenKey`, `InvalidScenario.writtenGivenKey`).
- No spec computed a string in the form of a created key that no running service created (`InvalidScenario.computedKey`).

`test` searches the orders that no line writes:

- Deadlines of one service due at the same time, and the steps of one processing that no cause orders.
  Two steps conflict when what they read and write overlaps, and `test` runs only the orders of conflicting steps (dynamic partial-order reduction).
- Which of the equal requests of one processing each handle of `requests` names.
  `test` runs every assignment.

When an order or an assignment changes the outcome, `test` reports `ChoiceDependent`.
Two outcomes are the same when each channel carries the same messages in the same order and the records are equal up to a renaming of created keys.

### When a trace matches a snapshot

`drive` from `@natsuzora-dev/tazuna/verify` controls only the implementation's world: the start, the clock, the messages that the implementation receives, and restarts.
The implementation creates its keys and request ids in its own way.

A trace *matches* a snapshot when all of the following hold:

- Its `in` lines equal the snapshot's `in` lines.
- The `out` lines after each `in` line pair one to one with the snapshot's.
  They keep the snapshot's order on each channel and no order across channels (`ordered_same_channel`).
  A trace line names no receiver, so `verify` takes the answers to one request, the events with one `resultOf`, and the events without `resultOf` each as one channel.
  The events of one group that `decide` returns have no order, even on one channel.
- One binding maps each value that the snapshot creates to one implementation value over the whole comparison.
  The binding is one to one within each domain: the request ids, and the keys of each entity (`compare_oneToOne`).

An implementation that reuses an existing request id or key for a new one does not match.
An implementation that uses a string of its input, such as an idempotency key, as a new key can match.

`verify` keeps every binding that agrees with the lines compared so far.
The counts in a bag can decide a binding: the snapshot's `[K1, K1, K2]` against the implementation's `[x, y, y]` binds `K1` to `y`.
Keys that only a later line tells apart wait for that line.
`verify` reports these cases:

- `Uncomparable.ambiguous`: the bindings give a value of an `in` line different implementation values, so the binding that `drive` chose decided what the implementation got.
- `Uncomparable.duplicateId`: an `out` request has the id of an earlier request.
- `Uncomparable.bindingLimit`: a line would make `verify` keep more than 256 bindings.

`test` compares outcomes the same way, so a spec without a `ChoiceDependent` violation fixes the order that `verify` asks of each channel.
Created keys are compared only up to renaming, so a spec must not compute a string in the form of a created key.

## Who fixes a violation

A definition's *contract* is what it promises: its inputs and outputs, its preconditions (`requires`), its postconditions (`ensures`), and its rejections.
The side that breaks a contract is at fault: the caller for a precondition, and the callee for a postcondition.

| Group | Reported by | Side at fault |
|---|---|---|
| `Malformed` | `check` | The spec. |
| `NonCanonical` | `check` | The spec. |
| `Restricted` | `check` | The spec. |
| `Illegal` | `check` | The spec. |
| `InvalidScenario` | `test` | The scenario: a line that cannot take place, a message that it leaves unstated, or an expectation of Then that does not hold. |
| `InvalidInput` | `test` | The scenario: a message that no sender could give the running service, including an external peer's answer that breaks the peer's contract. |
| `Fault` | `test` | The spec. |
| `BagOrderDependent` | `test` | The spec. |
| `ChoiceDependent` | `test` | The spec. |
| `Uncovered` | `test --coverage` | The scenarios. |
| `Mismatch` | `test`, `verify` | The implementation or external service whose trace differs, or, for `test`, the snapshot that differs from its scenario's simulation. |
| `Uncomparable` | `test`, `verify` | The trace whose `in` lines differ from the snapshot's or that pairs with it in more than one way, or, for `test`, the snapshot that has no scenario. |

## Detections

A *detection* does not cover every case.
When a detection reports a violation, the violation is real.
When it reports nothing, the violation can still exist.

`test` explores paths that append *moves* to each scenario, up to `--depth` moves.
A move is one act that faces the own service, with the network lines that it needs.
An explored path uses values from the scenarios and new ids, and it neither resends a command nor redelivers an event.

| Detection | What it leaves out |
|---|---|
| Violations on explored paths | Paths longer than `--depth`, and values that no scenario uses. |
| `Restricted` | A clock, random source, or locale that a spec function reaches by a name that `check` does not look for. |
| `BagOrderDependent` | Orders of a `Bag` other than the written one and its reverse. |
| `ChoiceDependent` | Orders and assignments beyond `ChoiceDependent.searchLimit`, and a difference in outputs that `verify` cannot compare, such as equal requests that get different answers. The records are still compared. |
| `InvalidInput` | Parts of an external peer's contract other than the requires that read only the input and the ensures that read no records. |
| `Uncovered` | Parts that only paths longer than `--depth` reach. |

## Assumptions

The guarantees hold only under the following assumptions.
tazuna detects a break of each assumption only partly or not at all.

- **Runtime.** The TypeScript runtime returns the same traces and violations as the Lean definitions.
  Diff tests compare the two only on tazuna's own example specs and traces, and for `test` on the paths that append up to two moves to the example scenarios.
- **Spec functions.** Spec functions are deterministic.
  They read no clock, random source, or mutable global state, and they receive the current time as an argument.
- **Types.** Each value in spec code has the type that the code declares.
  A result of a spec function depends neither on the order in which a `Bag` visits its values nor on the order of keys, as a comparison such as `a.id < b.id` would.
  `test` detects a dependence on `Bag` order only partly: it runs each spec function whose call visited a `Bag` of two or more values again with every `Bag` reversed, and reports `BagOrderDependent` when the two results differ up to a renaming of created keys.
- **Adapter.** The `Adapter` that `drive` drives the implementation through controls the implementation's whole world.
  The implementation reads the time only from the clock that `advanceTo` moves, and receives messages only through the adapter.
  The adapter reports only messages that the implementation received or sent, with the values that the implementation used.
  Its `settled` resolves only when the implementation has no work left that it can do before it gets a message or the clock moves.
  `drive` gives the next `in` line then, so an output that the implementation sends later falls in the group of a later input and does not match.
  An adapter that can only wait, such as one that drives a browser, bounds the wait and rejects with `Unsettled`.
- **External services.** Each external service keeps the contract that the spec assumes of it.
  `verify` checks this only on the traces of external services in the traces folder.
- **Opaque values.** An implementation treats the ids and keys that it did not create as opaque.
  Replacing them one to one in its inputs replaces them the same way in its outputs and changes nothing else.
  A running peer's implementation gets the values of other implementations, while its snapshot holds the values of the simulation, so its trace stands for both.
- **Reproducible implementations.** Given the same world, an implementation sends the messages of its recorded trace.
  `verify` compares each implementation's trace with its own snapshot, so the claim that several implementations together produce the simulated run rests on this assumption and the previous one.
- **Tools.** The Lean kernel, the TypeScript type checker, and Node.js are correct.

## Proven properties

Each item holds for every spec, and the theorems in `lean/Tazuna/Thm` that prove it follow in parentheses.
Machines and screens are statecharts, called *charts*.
A running chart is an *instance*.
A map state has one *copy* of its child states for each key of its items.

### Checks

- `check` passes only when each contract lists only members of its own service (`members_of_own_service`).
- `check` passes only when no chart sends a query to its own service (`queries_of_other_services`).
- `check` passes only when no chain of automations leads back to its start (`no_automation_returns`).
- `check` passes only when no unguarded `always` transition can reach its own source again (`unguarded_always_does_not_return`).
- `check` passes only when each command emits only events of its own service (`commands_emit_own_events`, `accepted_command_emits_own_events`).

### Simulation

- Then only adds violations. A scenario leaves the same traces, messages, and halt as the same scenario without Then, so a snapshot depends on Given and When alone (`then_only_reports`). The checks at the end of a run also only add violations (`simulate_reported`).
- A line changes no message in flight except the one that its handle names, and only a deliver, lose, or refuse line removes one (`line_keeps_leftInFlight`, `moving_line_keeps_others`).
- A message reaches its receiver only through a deliver, redeliver, or refuse line. Another line changes no running service's state unless it gives that service something to process (`line_keeps_states`).
- A deliver line whose message has an earlier message in flight on its channel delivers nothing and stops the simulation (`overtaking_delivery_halts`).
- An external peer's answer to a request that has not reached the peer sends nothing and stops the simulation (`external_answer_needs_delivery`).
- A halting violation stops the simulation, and the lines after it take no effect (`halting_report_stops`, `lines_after_stop_ignored`).
- No two createKey calls of the running services return the same key. Each line keeps every created key (`execute_keepsKeys`, `created_kept`), the `n`-th key of an entity is `<service>/<Entity>-<n>` (`created_distinct`), and no key that the scenario may write, such as a Given key, is ever created (`unwritten_not_created`, `execute_unwritten_not_created`).
- The order in which Given writes the records does not matter: a scenario that writes the same records in another order simulates alike (`simulate_records_perm`).

### Data validity

- The service normalizes the payload of each event that a command emits and the output of each query answer with the declared schema before it sends them (`decide_payloads_sorted_before_normalize`, `resolve_output_sorted_before_normalize`).
- An accepted command emits only events that its `decide` returned and its `emits` lists. An unlisted event halts the run (`accepted_emits_decided`, `unlisted_emitted_event_halts`).
- When the input of a command or query does not fit its schema, the service rejects it with `invalid-input` (`command_invalid_input_rejected`, `query_invalid_input_rejected`).
- A spec service never rejects a request from another spec service with `invalid-input` unless the definition declares it, because the sender checks the input first (`rejectionKinds_internal`).

### Statecharts

Charts follow the SCXML (W3C) algorithm.

- Entering a compound state enters its initial child (`enters_initial`).
- A transition exits states from the innermost and enters states from the outermost (`microstep_exits_in_exit_order`, `microstep_enters_in_entry_order`).
- In each atomic state, at most one transition runs for one event (`select_one_per_leaf`, `always_one_per_atomic`).
- When a transition of a state and a transition of its ancestor are both enabled, the transition of the state runs (`descendant_replaces_ancestor`, `leaf_selects_innermost`).
- A transition to an ancestor exits the ancestor (`ancestor_target_exits`).
- A transition to a descendant of its source exits the source when it reenters, and keeps it otherwise (`reenter_true_exits`, `reenter_false_not_exited`).
- An event that enables no transition changes nothing (`untaken_operation_changes_nothing`).
- A stopped instance processes no event (`stopped_machine_takes_no_event`).
- An event without a key reaches every copy of a map state (`keyless_payload_reaches_all`).
- When the copies of a map state have distinct keys, an event with a key reaches at most one copy (`keyed_payload_reaches_at_most_one`).

### Requests and deadlines of a state

- A deadline fires only while its state is active (`fires_only_in_active_state`).
- Leaving a state makes its awaited requests and queued commands stale (`leave_makes_requests_stale`, `leave_makes_queued_stale`).
- An answer to a stale request only ends the wait for it (`stale_answer_ignored`, `stale_command_answer_ignored`).
- A state that is exited before it sends its requests sends nothing (`exited_state_sends_nothing`).
- Stopping an instance cancels the deadlines and requests of its active states (`endWith_cancels_deadlines_and_requests`).

### Subscriptions and screens

- The service sends a new answer to a subscription only when the answer changes (`changed_answer_sent`, `unchanged_answer_not_sent`).
- The service sends no answer to an ended subscription (`ended_subscription_not_answered`).
- Opening a screen creates one child instance of the opened screen (`entering_opens_one_child`).
- An operation reaches a screen only when no modal screen that was opened later is still open, as in the WAI-ARIA modal dialog (`modal_child_covers`).
- A non-modal child screen leaves its parent operable (`nonmodal_child_lets_parent`).

### Time

- Processing a message never changes the current time. Only a clock line moves it (`drain_keeps_now`).
- Every line that processing a message writes carries the current time (`message_outputs_at_its_time`).
- A deadline due by the time that the clock moves to fires as a message of its own, at its time (`deadline_is_own_message`, `deadline_message_at_its_time`).
- Deadlines of one service due at the same time fire in the step order that `test` searches, whichever line moved the time (`chooseDeadline_stepOrder`).

### Processing and completion

- A command takes exactly one message to completion (`send_is_one_message`).
- A failed postcondition or invariant is a `Fault` of the command after which it fails (`failed_ensures_blames_command`, `entity_invariant_reported_iff`, `service_invariant_reported_iff`).
- A rejected command writes no record and emits no event (`rejected_command_changes_nothing`).
- An accepted command writes its records before any reaction to its events runs (`accepted_command_writes_then_queues_reactions`, `reaction_reads_current_records`).
- Processing that reaches a limit that tazuna sets halts with the `Fault` of that limit (`drain_at_work_limit`, `settle_halts_at_round_limit`, `exitOne_at_depth_limit`, `fireDue_at_deadline_limit`).

### Ordering

- Spec functions read the keys of an entity in one order, whatever order the records were written in (`keys_perm`).
- The elements of a bag or set, and the elements with equal keys in an array sorted by a key, are in the order of their canonical JSON (`bag_or_set_array_sorted`, `sortByKey_equal_keys_in_canonical_order`).
- A snapshot orders two `out` lines after one `in` line only when they travel on one channel (`ordered_same_channel`), and never two lines of one group of events that `decide` returns (`group_lines_unordered`).

### Identity

Request ids follow the `Idempotency-Key` HTTP header (IETF).

- Each input keeps the keys of a keyed entity distinct (`send_keysDistinct`, `message_keysDistinct`).
- A reference that does not resolve is a `Fault` (`dangling_ref_reported_iff`).
- When a command arrives again with the same id and the same input, the service answers it with the first answer and does not run it again (`resent_command_gets_first_answer`, `resent_command_ignores_decide`).
- The service rejects a command that reuses an id with a different input (`reused_id_rejected`).
- When an event arrives again with the same id, the service does not process it again (`redelivered_event_not_processed`).
- The service answers a repeated query again, because a query has no identity (`query_processed_again`).

### Restart

- After a restart, a service keeps its records, its command answers, its delivered events, and its created keys. It discards its instances, deadlines, awaited requests, and subscriptions (`restart_keeps`).
- A restart reads nothing of the state that it discards (`restart_forgets`).

### Comparison

- A snapshot matches a run when their lines have equal canonical JSON, whatever the order of object fields (`compareSnapshot_eq_none_iff`, `compareSnapshot_reordered`).
- Every binding that a trace comparison ends with is one to one within each domain, and keeps every pair that an earlier step bound (`compare_oneToOne`, `compareGroups_extends`).
