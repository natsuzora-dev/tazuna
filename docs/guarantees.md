# Guarantees

Lean definitions state what a spec means, and Lean theorems prove properties of that meaning.
tazuna guarantees only what the Lean theorems prove.

Precedent: AWS Cedar, whose properties are proven in Lean and whose Rust implementation is tested against the Lean model.

## Terms

A *spec* defines services.
A service interacts with the world only through messages.
It receives requests (commands, queries, and subscriptions), events from other services, user operations on its screens, the current time, and restarts from its environment.
It sends answers, events, and requests of its own.
The sequence of these messages, each with its time, is the service's *trace*.

A *scenario* of a service, the *own* service, has three parts:

- *Given* arranges the start: the start time, the records of the own service, and every other service that the own service exchanges messages with, each as a *running peer* (`run`), an *external peer* (`external`), or a skipped peer (`skip`).
- *When* places *lines* in order.
  Each line is one act of an actor: the client or a peer sends, the user operates a screen, the network delivers a message, the clock advances, or the host restarts the own service.
  A line returns a *handle*, through which later lines and Then name the line and what it caused.
- *Then* states what the own service did on the lines of When.

The own service and its running peers are the *participants* of one *simulation*.
They share one clock, and a message between two of them stays *in flight* until a network line delivers, redelivers, loses, or fails it.
Messages travel on *channels*: a request, its answers, its end, and the events that name it as their `resultOf` share the request's channel, and an event without `resultOf` travels on the channel of its sender and receiver.
The simulation is deterministic: the scenario writes every choice that nobody's code makes, such as which message arrives next, when the time advances, and which of two deadlines due at the same time fires first.

The trace of the own service is the scenario's *snapshot*, and the trace of each running peer is a snapshot of its own.
tazuna has three tools that report violations:

- `check` reads the spec and reports its violations without running it.
- `test` simulates every scenario and compares each participant's trace with its snapshot.
- `verify` compares the traces that `drive` from `@natsuzora-dev/tazuna/verify` makes of an implementation with the snapshots.

A *violation* is a problem that a tool reports.
Each violation has a kind, such as `Fault.failedEnsures`.
The part of the kind before the dot is the violation's *group*.
A kind's name and data, with its doc comment where they do not suffice, state what the kind means.
A run stops at a violation of a *halting* kind, because the behavior after that violation is undefined.

## What a passing tool means

A tool *passes* when it reports no violation.

- When `check` passes, the spec type-checks and has no violation of the groups that `check` reports.
- When `test` passes, `check` passes, every line of every scenario takes place, every expectation of Then holds, and each participant's trace equals its snapshot.
- When `test` and `verify` both pass with the same spec and snapshots, the trace that `drive` makes of the implementation in each scenario matches the snapshot, for the own service and for each running peer that has an implementation.

When, in addition, the [assumptions](#assumptions) hold, the implementation sends the messages that the spec defines for the lines of each scenario.
tazuna guarantees nothing about lines that no scenario contains.

### When a scenario simulates

Lean defines the simulation in `lean/Tazuna/Sim`, and `Sim.Report` holds what it reports about a scenario.
When `test` reports no `Report` violation, the scenario stated everything that happened between the participants:

- every message between two participants reached its receiver by a line of When, or the scenario names it as lost, failed, or in flight at the end (`Report.leftInFlight`);
- a message never overtook an earlier one on its channel (`Report.overtaking`);
- each line of a running peer states a message that its run sent, and each answer of an external peer answers a request that reached it; an external peer's request that the scenario delivered is answered or left unanswered, not both (`Report.awaitingAnswer`, `Report.repeatedAnswer`);
- an event's `resultOf` names a request that its emitter received (`Report.unreceivedRequest`), and the receiver took that request's answer before the event (`InvalidInput.resultOfUnansweredRequest`);
- each message that the scenario names as in flight at the end, it names once (`Report.repeatedInFlight`);
- the clock only advanced (`Report.notLater`);
- the scenario wrote no key that a participant creates, of the form `<participant>/<Entity>-<n>` (`Report.writtenKey`).

No Lean theorem states properties of the simulation yet.

### When a trace matches a snapshot

`drive` controls only the implementation's world, the start, the clock, and the messages it receives, so the implementation creates its keys and request ids in its own way; `src/verify/harness.ts` states how.
A trace *matches* a snapshot when its `in` lines equal the snapshot's exactly and the `out` lines after each pair up one to one, with each value that the snapshot creates bound to one implementation value over the whole comparison.
The binding is one-to-one within each domain, the request ids and the keys of each entity (`compare_oneToOne`), so an implementation that reuses an existing request id or key of an entity for a new one differs, while one that uses a string of an input, such as an idempotency key, as a new key does not.
When the snapshot's lines leave the choice among equal implementation requests or keys open and an `in` line names one of them, `verify` reports the line as `Uncomparable.ambiguous` unless the snapshot's `in` lines use those values alike; `lean/Tazuna/Verify/Compare.lean` defines the comparison.

## Who fixes a violation

The side that breaks a contract is at fault: the caller for a precondition, and the callee for a postcondition.
A definition's *contract* is what it promises to its callers: its inputs and outputs, its preconditions (`requires`), its postconditions (`ensures`), and its rejections.
The following table names the side at fault for each group.

| Group | Reported by | Side at fault |
|---|---|---|
| `Malformed` | `check` | The spec. |
| `NonCanonical` | `check` | The spec. |
| `Restricted` | `check` | The spec. |
| `Illegal` | `check` | The spec. |
| `Report` | `test` | The scenario: a line that cannot take place, a message that it leaves unstated, or an expectation of Then that does not hold. |
| `InvalidInput` | `test` | The scenario: a message that no sender could give the participant, including an external peer's answer that breaks the contract that the spec assumes of it. |
| `Fault` | `test` | The spec. |
| `OrderDependent` | `test` | The spec. |
| `ChoiceDependent` | `test` | The spec. |
| `Uncovered` | `test --coverage` | The scenarios. |
| `Mismatch` | `test`, `verify` | The implementation or external service whose trace differs, or, for `test`, the snapshot that differs from its scenario's simulation. |
| `Uncomparable` | `test`, `verify` | The trace whose `in` lines differ from the snapshot's or that pairs with it in more than one way, or, for `test`, the snapshot that has no scenario. |

Precedent: Design by Contract (Bertrand Meyer), where a precondition binds the caller and a postcondition binds the callee.

## Detections

A *detection* is a report that does not cover every case.
When a detection reports a problem, the problem is real.
When a detection reports nothing, the problem can still exist.

`test` explores paths that append moves to each scenario.
A move is one act that faces the own service, with the network lines it needs.
An explored path uses values from the scenarios and new IDs, and it neither resends a command nor redelivers an event.

| Detection | What it leaves out |
|---|---|
| Violations that `test` finds on explored paths | Paths longer than `--depth`, and values that no scenario uses. |
| `Restricted` | A clock, random source, or locale that a spec function reaches by another name than the ones that `check` looks for in the spec's source. |
| `OrderDependent` | Orders of a `Bag` other than the written one and its reverse. |
| `ChoiceDependent` | Orders of steps and of tied deadlines beyond the `ChoiceDependent.searchLimit` of one processing. |
| `InvalidInput` | An external peer's answer is checked only against the requires that read the input alone and the ensures that read no records. |
| `Uncovered` | Parts that only paths longer than `--depth` reach. |

## Assumptions

The guarantees hold only under the following assumptions.
tazuna detects breaks of each assumption only partly or not at all.

- **Runtime.** The TypeScript runtime returns the same traces and violations as the Lean definitions.
  The runtime and the Lean definitions are compared only on tazuna's own example specs and traces, not on yours.
  For `test`, the comparison covers the example scenarios and the paths that append up to two moves to them.
  For `check` and `verify`, it covers the example specs and traces.
- **Spec functions.** Spec functions are deterministic: they read no clock, random source, or mutable global state, and receive the current time as an argument.
- **Types.** Each value in spec code has the type that the code declares.
  A result of a spec function does not depend on the order in which a `Bag` visits its values, which a callback can still see through a variable that it changes, nor on the order of keys, which a comparison such as `a.id < b.id` sees.
  `test` detects a dependence on the order of a `Bag` only partly, as `OrderDependent`: it asks a spec function whose call ran a callback of a `Bag` with two or more values again, with every `Bag` visiting its values in reverse order, and compares the two answers, each key that a call creates by its entity alone.
- **Adapter.** The adapter that `drive` drives the implementation through reports only messages that the implementation received or sent, with the values that the implementation used, and it controls the implementation's whole world: the implementation reads the time only from the clock that `advanceTo` moves, and receives messages only through the adapter.
  Its `settled` resolves only when the implementation has no work left that it can do before it gets a message or the clock moves; `drive` gives the next `in` line then, so an output that the implementation would still send lands in the group of a later input and compares as a mismatch.
  An adapter that can only wait for that, such as one that drives a browser, bounds the wait and rejects with `Unsettled` when the bound passes.
- **External services.** Each external service keeps the contract that the spec assumes of it.
  `verify` detects a break of this assumption only on the traces of external services in its folder.
- **Opaque values.** An implementation treats the IDs and keys that it did not create as opaque: replacing them one to one in its inputs replaces them the same way in its outputs and changes nothing else.
  A running peer's implementation receives the values of another implementation, while its snapshot holds the values of the simulation, so its trace stands for what it does with either.
- **Reproducible implementations.** One recorded run represents the implementation: given the same world, the implementation sends the messages of that trace.
  `verify` relates each implementation's trace to its own snapshot, so that two implementations together produce the simulated execution rests on this assumption and the previous one.
- **Tools.** The Lean kernel, the TypeScript type checker, and Node.js are correct.

## Proven properties

Each section lists properties that hold for every spec, each with the theorems in `lean/Tazuna/Thm` that prove it.

Machines and screens are statecharts, called *charts*.
A running chart is an *instance*.
A map state has one *copy* of its child states for each key of its items.

### Checks

- `check` passes the contracts only when each contract lists only the members of its own service (`members_of_own_service`).
- `check` passes the charts only when no chart sends a query to its own service (`queries_of_other_services`).
- `check` passes the automations only when no chain of automations leads back to its start (`no_automation_returns`).
- `check` passes the charts only when no unguarded `always` transition can reach its own source again (`unguarded_always_does_not_return`).
- `check` passes the commands only when each command emits only events of its own service (`commands_emit_own_events`, `accepted_command_emits_own_events`).

### Data validity

- Before sending, the service normalizes the payload of each event that a command emits and the output of each query answer with the declared schema (`decide_payloads_sorted_before_normalize`, `resolve_output_sorted_before_normalize`).
- An accepted command emits only events that its decide returned, all listed in its `emits`; an unlisted event halts the run (`accepted_emits_decided`, `unlisted_emitted_event_halts`).
- When the input of a command or query does not fit its schema, the service rejects it with `invalid-input` (`command_invalid_input_rejected`, `query_invalid_input_rejected`).
- A request to a spec service is never rejected with `invalid-input` unless its definition declares it: the sender checks the input first (`rejectionKinds_internal`).

Precedent: "Parse, don't validate" (Alexis King), where a value is checked once at the boundary and trusted inside.

### Statecharts

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

Precedent: SCXML (W3C), whose algorithm fixes the entry and exit order and the conflict resolution of transitions.

### Requests and deadlines of a state

- A deadline fires only while its state is active (`fires_only_in_active_state`).
- Leaving a state makes its awaited requests and queued commands stale (`leave_makes_requests_stale`, `leave_makes_queued_stale`).
- An answer to a stale request only ends the wait for it (`stale_answer_ignored`, `stale_command_answer_ignored`).
- A state that is exited before it sends its requests sends nothing (`exited_state_sends_nothing`).
- Stopping an instance cancels the deadlines and requests of its active states (`endWith_cancels_deadlines_and_requests`).

Precedent: SCXML (W3C), which cancels an invoked service when the state that invoked it is exited.

### Subscriptions and screens

- The service sends a new answer to a subscription only when the answer changes (`changed_answer_sent`, `unchanged_answer_not_sent`).
- The service sends no answer to an ended subscription (`ended_subscription_not_answered`).
- Opening a screen creates one child instance of the opened screen (`entering_opens_one_child`).
- An operation reaches a screen only when no modal screen that was opened later is still open (`modal_child_covers`).
- A non-modal child screen leaves its parent operable (`nonmodal_child_lets_parent`).

Precedent: the modal dialog of the WAI-ARIA Authoring Practices (W3C), which makes the content outside the dialog inert.

### Time

- Processing a message never changes the current time; only a clock line advances it (`drain_keeps_now`).
- Every line that processing a message writes carries the current time (`message_outputs_at_its_time`).
- A deadline due by the time that the clock advances to fires as a message of its own, at its time (`deadline_is_own_message`, `deadline_message_at_its_time`).
- Of deadlines due at the same time while a clock line advances the clock, the next entry of the line's `order` chooses the one that fires (`chooseDeadline_named`), and a tie that no entry decides is reported instead of decided (`chooseDeadline_required`).
- Deadlines that become due at the same time while a service processes any other line tie inside that service, where no line can order them; they fire in the order of the step order that `test` searches (`chooseDeadline_stepOrder`), and `test` reports `ChoiceDependent` when another order changes the result.

Precedent: deterministic simulation testing (FoundationDB), where the simulator supplies the clock.

### Processing and completion

- A command takes exactly one message to completion (`send_is_one_message`).
- A failed postcondition or invariant is reported as a `Fault` of the command after which it fails (`failed_ensures_blames_command`, `entity_invariant_reported_iff`, `service_invariant_reported_iff`).
- A rejected command writes no record and emits no event (`rejected_command_changes_nothing`).
- An accepted command writes its records before any reaction to its events runs (`accepted_command_writes_then_queues_reactions`, `reaction_reads_current_records`).
- Processing that reaches a limit that tazuna sets halts with the `Fault` of that limit (`drain_at_work_limit`, `settle_halts_at_round_limit`, `exitOne_at_depth_limit`, `fireDue_at_deadline_limit`).

Precedent: the run-to-completion step of UML state machines (OMG).

### Ordering and determinism

- Spec functions read the keys of an entity in one order, whatever order the records were written in (`keys_perm`).
- The elements of a bag or set, and the elements with equal keys in an array sorted by a key, are in the order of their canonical JSON, whatever order the spec built them in (`bag_or_set_array_sorted`, `sortByKey_equal_keys_in_canonical_order`).
- Two lines of one group of the events that `decide` returns have no order between them, so a snapshot does not order them (`group_lines_unordered`).

Precedent: CHESS (Madanlal Musuvathi and others), which makes each scheduling choice an input to a run.

### Identity

- Each input keeps the keys of a keyed entity distinct (`send_keysDistinct`, `message_keysDistinct`).
- When a reference does not resolve, `test` reports it under `Fault` (`dangling_ref_reported_iff`).
- When a command arrives again with the same ID and the same input, the service answers it with the first answer and does not run it again (`resent_command_gets_first_answer`, `resent_command_ignores_decide`).
- The service rejects a command that reuses an ID with a different input (`reused_id_rejected`).
- When an event arrives again with the same ID, the service does not process it again (`redelivered_event_not_processed`).
- The service answers a repeated query again, because a query has no identity (`query_processed_again`).

Precedent: the `Idempotency-Key` HTTP header (IETF).

### Restart

- After a restart, a service keeps its records, its command answers, its delivered events, and its created keys, and discards its instances, deadlines, awaited requests, and subscriptions (`restart_keeps`).
- A restart reads nothing of the part of the state that it discards (`restart_forgets`).

Precedent: the Restart action of the Raft TLA+ spec (Diego Ongaro).

### Comparison

- A snapshot matches a run when their lines have equal canonical JSON, whatever the order of object fields (`compareSnapshot_eq_none_iff`, `compareSnapshot_reordered`).
- The binding of a trace comparison is one-to-one within each domain of values, and every pair that any step bound stays in it (`compare_oneToOne`, `compareGroups_extends`).
