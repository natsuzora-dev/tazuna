# Guarantees

Lean definitions in [`lean/Tazuna`](../lean/Tazuna) state what a spec means, and Lean theorems prove properties of that meaning.
tazuna guarantees only what the theorems prove, under the [assumptions](#assumptions) below.
[Concepts](concepts.md) explains the ideas that this page refers to.

## Terms

A service interacts with the world only through messages.
It receives requests (commands, queries, and subscriptions), events, user operations on its screens, the current time, and restarts.
It sends answers, events, and requests of its own.
The sequence of these messages, each with its time, is the service's *trace*.

A scenario's own service and its running peers (`run`) are the *running services* of one *simulation*.
They share one clock.
A message to or from a running service stays *in flight* until a line of `w.net` decides its fate.
The simulation is deterministic: the scenario writes every choice that no service's code makes, such as which message arrives next and when the time advances.

Messages travel on *channels*.
A request, its answers, its end, and the events that name it as their `resultOf` share the request's channel.
An event without `resultOf` travels on the channel of its sender and receiver.
Messages on one channel keep their order, and messages on different channels keep none.
Of two events on one channel, the later keeps its place only when the step that emitted it is the earlier's step, in a later group of its `decide`, or one that the earlier's step caused, or when a clock line sent it after the earlier.
A deadline counts as caused by the step that entered its state.
Events of steps that no cause chain links, such as two map copies or two tied deadlines, keep no order.
A snapshot keeps no order between a request's answers and its result events, although the simulation delivers them on one channel.

The trace of the own service in a scenario is the scenario's *snapshot*, and the trace of each running peer is a snapshot of its own.

A *violation* is what a command reports.
Each violation has a kind, such as `Fault.failedEnsures`, and the part before the dot is its *group*.
The doc comment of a kind states what it means.
A run stops at a violation of a *halting* kind, because after it the spec's behavior is undefined or the scenario describes no run.
`halts` in `lean/Tazuna/Service/Fault.lean`, `lean/Tazuna/Service/InvalidInput.lean`, and `lean/Tazuna/Sim/InvalidScenario.lean` defines which kinds halt.

## What a passing command means

A command *passes* when it reports no violation.
tazuna aims to report each mistake with the earliest tool that can find it, in this order: the TypeScript type checker, `check`, the simulation in `test`, the exploration in `test`, and `verify`.

- When `check` passes, every spec file type-checks under the nearest tsconfig.json, and the spec has no violation of the groups that `check` reports.
  `test`, `verify`, and `view` run the checks of `check` first and stop at its violations, and `drive` and `verifyTraces` take only a spec that `checkSpec` returned as checked.
- When `test` passes, `check` passes, every line of every scenario takes place, every expectation of Then holds, and each running service's trace equals its snapshot.
  No explored path of up to `--depth` moves after a scenario reports a violation.
- When `test` and `verify` both pass with the same spec and snapshots, the trace that `drive` makes of the implementation in each scenario matches the snapshot.
  This holds for the own service and for each running peer that has an implementation.

When the assumptions also hold, the implementation sends the messages that the spec defines for the lines of each scenario.
tazuna guarantees nothing about lines that no scenario contains.

### When a scenario simulates

When `test` reports no `InvalidScenario` violation, the scenario states everything that happened between the running services.
Each `InvalidScenario` kind is one rule of that statement, and its doc comment states the rule.

`test` searches the orders that no line writes:

- Deadlines of one service due at the same time, the messages that one line delivers to one service, and the steps of one processing that no cause orders.
  A machine receives each event of one group that `decide` returns in a step of its own, so the order of a group is one of these orders.
  Two steps conflict when what they read and write overlaps, and `test` runs only the orders of conflicting steps (dynamic partial-order reduction).
  A tied deadline, and a message that a line delivers with others, is a message of its own, so what it reads and writes includes every step of that message and what the hold and invariant checks and the subscription answers after the message read (`involved` in `lean/Tazuna/Explore/Instrument.lean`).
- Equal messages that one line delivers to one service are not searched.
  A service reads a received id only to route a message, to answer it, and to tell one it processed before, so their other order is the same run with their ids swapped, and `test` compares that run without executing it (`ChoiceDependent.equalMessages`).

When an order changes the outcome, `test` reports `ChoiceDependent`.
Two outcomes are the same when both halt with the same violation, or when neither halts, their lines pair one to one with equal contents and the same `after` through the pairing, and the records are equal up to a renaming of created keys.
The renaming maps each key that one run created to a key that the other run created for the same entity, never to another string, and it maps the key alike wherever the key appears.
Lines that a service wrote for messages that one line delivered compare by message, as `verify` pairs a trace's `in` lines with the snapshot's, and not by when the service processed them.

### When a trace matches a snapshot

`drive` from `@natsuzora-dev/tazuna/verify` controls only the implementation's world: the start, the clock, the messages that the implementation receives, and restarts.
The implementation creates its keys and request ids in its own way.

A trace *matches* a snapshot when all of the following hold (`compare_matches`):

- Its `in` lines pair in order with the snapshot's `in` lines, at equal times.
- The `out` lines after each `in` line pair one to one with the snapshot's, each pair equal under the binding.
  A one-to-one pairing, which can be another one, pairs them at equal times and keeps the order that each snapshot line's `after` names.
  `after` names only lines on one channel, and never two events at one time of one group that `decide` returns or of steps that no cause chain links (`ordered_same_channel`, `group_lines_unordered`, `independent_unordered`).
  A trace line names no receiver, so `verify` takes the answers to one request, the events with one `resultOf`, and the events without `resultOf` each as one channel.
- One binding maps each value that the snapshot creates to one implementation value over the whole comparison.
  The binding is one to one within each domain: the request ids, and the keys of each entity.
  Paired lines have the same type, direction, and name, and their contents, and the ids of `in` lines and outgoing requests, are equal up to the binding (`contentMatch_renamed`).

An implementation that reuses an existing request id or key for a new one does not match.
An implementation that uses a string of its input, such as an idempotency key, as a new key can match.

`verify` keeps every binding that agrees with the lines compared so far.
The counts in a bag can decide a binding: the snapshot's `[K1, K1, K2]` against the implementation's `[x, y, y]` binds `K1` to `y`.
Keys that only a later line tells apart wait for that line.
When the bindings cannot decide what the implementation gets, or a trace cannot be compared at all, `verify` reports an `Uncomparable` kind, and its doc comment states the case.

`test` compares outcomes the same way, `after` included, so a spec without a `ChoiceDependent` violation fixes the `after` that `verify` checks.
An implementation's trace has no `after` or `created`, and `verify` reports a trace line that has either as `Uncomparable.lineSchema`.
Because created keys compare only up to renaming, a string that a spec computes in the form of a created key is `Fault.computedKey`.

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
| `Uncomparable` | `test`, `verify` | The trace whose `in` lines differ from the snapshot's or that pairs with it in more than one way, or, for `test`, a snapshot without a scenario or a scenario without a snapshot. |

## Detections

A *detection* is a check that can miss violations.
When a detection reports a violation, the violation is real.
When it reports nothing, the violation can still exist.

`test` explores paths of up to `--depth` *moves* after each scenario.
A move is one act that faces the own service, with the network lines that it needs.
An explored path uses values from the scenarios and new ids, and it neither resends a command nor redelivers an event.

| Detection | What it leaves out |
|---|---|
| Violations on explored paths | Paths longer than `--depth`, and values that no scenario uses. |
| `Restricted` | A clock, random source, or locale that a spec function reaches by a name that `check` does not look for, or through a package that the spec imports. `check` also reads the local files that the spec imports by a relative path. |
| `BagOrderDependent` | Orders of a `Bag` other than the written one and its reverse, and answers with too many renamings of created keys to compare, which it reports as `BagOrderDependent.uncomparable`. |
| `ChoiceDependent` | Orders beyond `ChoiceDependent.searchLimit`. The order of two ready steps with equal step names, which the search takes as one step: such steps differ only in the step that caused them or, for answers, in which of two equal requests each answers. A difference in outputs that `verify` cannot compare, such as equal requests that get different answers, although the records are still compared. Records with too many renamings of created keys to compare are reported as `ChoiceDependent.uncomparable`. |
| `InvalidInput` | Parts of an external peer's contract other than the requires that read only the input and the ensures that read no records. |
| `Uncovered` | Parts that only paths longer than `--depth` reach. |

## Assumptions

The guarantees hold only under the following assumptions.
tazuna detects a break of each assumption only partly or not at all.

- **Runtime.** The TypeScript runtime returns the same traces and violations as the Lean definitions.
  Diff tests compare the two only on tazuna's own example specs and traces, and for `test` on the paths of up to two moves after the example scenarios.
  The theorems are about the Lean definitions with pure spec functions (`Functions Id`), and about a scenario's start only through hypotheses such as distinct Given keys.
  `test` runs the definitions with the spec functions of the TypeScript runtime and passes `verify`'s comparison to the exploration, so its runs rest on this assumption.
- **Spec functions.** Spec functions are deterministic.
  They read no clock, random source, or mutable global state, and they receive the current time as an argument.
  A result of a spec function depends neither on the order in which a `Bag` visits its values nor on the order of keys, as a comparison such as `a.id < b.id` would.
  `test` detects a dependence on `Bag` order only partly.
  It runs each spec function whose call visited a `Bag` of two or more values again with every `Bag` reversed, and reports `BagOrderDependent` when the two results differ up to a renaming of created keys.
- **Types.** Each value in spec code has the type that the code declares.
- **Adapter.** The `Adapter` that `drive` drives the implementation through controls the implementation's whole world.
  The implementation reads the time only from the clock that `advanceTo` moves, and receives messages only through the adapter.
  The adapter reports only messages that the implementation received or sent, with the values that the implementation used.
  Its `settled` resolves only when the implementation has no work left that it can do before it gets a message or the clock moves.
  `drive` gives the next `in` line then, so an output that the implementation sends after that is compared with the outputs of a later input, and does not match.
  An adapter that can only wait, such as one that drives a browser, bounds the wait and rejects with `Unsettled`.
- **External services.** Each external service keeps the contract that the spec assumes of it.
  `verify` checks this only on the traces of external services in the traces folder.
  An external command's `ensures` is checked once, at the end of the scenario or trace, with all its result events.
  An external query's `ensures` is checked when its answer arrives.
- **Opaque values.** An implementation treats the ids and keys that it did not create as opaque.
  Replacing them one to one in its inputs replaces them the same way in its outputs and changes nothing else.
  A running peer's implementation gets the values of other implementations, while its snapshot holds the values of the simulation, so `verify` assumes that the implementation behaves the same with either set of values.
- **Reproducible implementations.** Given the same world, an implementation sends the messages of its recorded trace.
  `verify` compares each implementation's trace with its own snapshot, so the claim that several implementations together produce the simulated run rests on this assumption and the previous one.
- **Tools.** The Lean kernel, the TypeScript type checker, and Node.js are correct.
  The Lean build fails on `sorry` and on any axiom other than `propext`, `Classical.choice`, and `Quot.sound`, so no theorem rests on an unproven step.

## Properties without a theorem

No theorem proves the following items yet.
Each holds by the Lean definition that it names, or only in the TypeScript runtime.

- Processing that reaches a limit that tazuna sets halts with the `Fault` of that limit (`drain` in `lean/Tazuna/Service/Chart/Macrostep.lean`, `settle` in `lean/Tazuna/Service/Chart/Always.lean`, `exitOne` in `lean/Tazuna/Service/Chart/Exit.lean`, `fireDue` in `lean/Tazuna/Service/Queue.lean`).
- The service answers a repeated query again, because a query has no identity (`call` in `lean/Tazuna/Service/Input.lean`).
- A refuse line gives the sender the `unavailable` answer (`take` in `lean/Tazuna/Sim/Run.lean`).
- A halting `Fault` or `InvalidInput` stops the simulation (`stopped` in `lean/Tazuna/Sim/Network.lean`).
- A clock line publishes the subscription answers that the new time changes (`fireTo` in `lean/Tazuna/Sim/Run.lean`).
- Only a clock line moves the current time (`fireTo` in `lean/Tazuna/Sim/Run.lean`).
- A command is processed as one message (`send` in `lean/Tazuna/Service/Input.lean`).
- Several open instances of one screen are each operable: an operation names its instance by the line that opened it (`operate` in `lean/Tazuna/Service/Input.lean`).
- A message carries its value as the sender wrote it, only the receiver parses it, and a spec service's `invalid-input` answer to another spec service is the sender's `Fault` (`checkAnswer` in `lean/Tazuna/Service/Input.lean`).
- A restart ends every subscription for `verify`, which expects the first answer of a subscription with the same id after it (`withoutRepeatedAnswers` in `lean/Tazuna/Verify/Compare.lean`).
- Spec functions read the keys of an entity in one order, whatever order the records were written in.
  Only the TypeScript runtime orders them: the Lean definitions give spec functions the records in write order.

## Proven properties

Each item holds for every spec, and the theorems in `lean/Tazuna/Thm` that prove it follow in parentheses.
Machines and screens are statecharts, called *charts*.
A running chart is an *instance*.
A map state has one *copy* of its child states for each key of its items.

### Simulation

- Then only adds violations. A scenario leaves the same traces, messages, and halt as the same scenario without Then, so a snapshot depends on Given and When alone (`then_only_reports`). The checks at the end of a run also only add violations (`simulate_reported`).
- A line changes no message in flight except those that its handle names, and only a deliver, lose, or refuse line removes one (`line_keeps_leftInFlight`, `moving_line_keeps_others`).
- Only a line that gives a running service something to process changes its state: a client's request, end, or resend, an operation, a clock or restart line, or a deliver, redeliver, or refuse line (`line_keeps_states`).
- A deliver line whose first message has an earlier message in flight that the line does not name and that must arrive first, on its channel and not an event of a step that no cause chain links to its own, delivers nothing and stops the simulation (`overtaking_delivery_halts`).
- An external peer's answer whose first request has not reached the peer sends nothing and stops the simulation (`external_answer_needs_delivery`).
- A halting `InvalidScenario` violation stops the simulation, and once the simulation stops, the steps of the later lines take no effect (`halting_report_stops`, `lines_after_stop_ignored`).
- No two createKey calls of one service return the same key. Each line keeps every created key (`execute_keepsKeys`, `created_kept`), the `n`-th key of an entity is `<owner>/<Entity>-<n>` (`created_form`, `created_distinct`), and no key that the scenario may write, such as a Given key, is ever created for an entity that is not a single entity, provided the service's state names the service as the owner of its keys, which `World.start` sets but no theorem proves (`unwritten_not_created`, `execute_unwritten_not_created`).
- The order in which Given writes the records does not matter: a scenario that writes the same records, no two with one key, in another order simulates alike (`simulate_records_perm`).
- The audits by which `test` finds `BagOrderDependent` and `ChoiceDependent` change no run of the pure definitions: a service whose spec functions are audited starts, processes each input, and checks the end of a run as it does without the audit (`instrument_agrees`, `begin_agrees`, `send_agrees`, `call_agrees`, `subscribe_agrees`, `endSubscription_agrees`, `receive_agrees`, `answerIn_agrees`, `operate_agrees`, `fireDue_agrees`, `publish_agrees`, `restart_agrees`, `checkResults_agrees`).

### Data validity

- An accepted command emits exactly the events that its `decide` returned, each once, with its payload normalized by the declared schema, in the groups that `decide` returned. Every event is one that `emits` lists, and an unlisted event halts the run (`accepted_emits_decided`, `unlisted_emitted_event_halts`).
- The service normalizes the output of each query answer with the declared schema (`resolve_output_sorted_before_normalize`).
- When the input of a command or query does not fit its schema, the service rejects it with `invalid-input` (`command_invalid_input_rejected`, `query_invalid_input_rejected`).

### Statecharts

Charts have these properties of the SCXML (W3C) algorithm: a chart enters its initial states, a microstep exits descendants before ancestors and enters ancestors before descendants, it takes only transitions that active leaves pick, in leaf order, a leaf picks a transition of its innermost state that takes the event, and a transition to an ancestor exits it (`enters_initial`, `microstep_exits_in_exit_order`, `exitOrder_descendants_first`, `microstep_enters_in_entry_order`, `entryOrder_ancestors_first`, `select_follows_leaves`, `select_picked_by_leaf`, `leaf_selects_innermost`, `ancestor_target_exits`, `untaken_operation_changes_nothing`).
The following items are tazuna's own:

- A transition to a descendant of its source exits the source when it reenters, and keeps it otherwise (`reenter_true_exits`, `reenter_false_not_exited`).
- A stopped instance processes no event (`stopped_machine_takes_no_event`).
- Of the copies of a map state, the reach filter keeps every copy for an event without a key (`keyless_payload_reaches_all`), and at most one copy for an event with a key when the copies have distinct keys (`keyed_payload_reaches_at_most_one`).

### Requests and deadlines of a state

- A deadline fires only while its state is active (`fires_only_in_active_state`).
- Leaving a state makes its awaited requests and queued commands stale (`leave_makes_requests_stale`, `leave_makes_queued_stale`).
- An answer to a stale request only ends the wait for it (`stale_answer_ignored`, `stale_command_answer_ignored`).
- A state that is exited before it sends its requests sends nothing (`exited_state_sends_nothing`).
- When every deadline and live request of an instance belongs to one of its active states, stopping the instance cancels them all (`endWith_cancels_deadlines_and_requests`).

### Subscriptions and screens

- When the service publishes, it sends a new answer to a subscription only when the answer changes (`changed_answer_sent`, `unchanged_answer_not_sent`).
- Publishing sends no answer to a subscription id that no open subscription has (`ended_subscription_not_answered`).
- Opening a screen creates one child instance of the opened screen (`entering_opens_one_child`).
- Among the screens open above an operated screen, a modal one covers it, as in the WAI-ARIA modal dialog (`modal_child_covers`), and non-modal ones leave it operable (`nonmodal_child_lets_parent`).

### Time

- The steps of a message never change the current time (`drain_keeps_now`).
- Every line that the steps of a message and the checks after them write carries the current time (`message_outputs_at_its_time`).
- A deadline due by the time that the clock moves to fires as a message of its own, at its time (`deadline_message_at_its_time`).
- Deadlines of one service due at the same time fire in the step order that `test` searches, whichever line moved the time (`chooseDeadline_stepOrder`).

### Processing and completion

- A failed postcondition or invariant is a `Fault` of the command after which it fails (`failed_ensures_blames_command`, `entity_invariant_reported_iff`, `service_invariant_reported_iff`).
- A rejected command writes no record and emits no event (`rejected_command_changes_nothing`).
- An accepted command leaves exactly the records that applying its emitted events gives (`accepted_command_writes_then_queues_reactions`).

### Ordering

- The elements of a bag or set, and the elements with equal keys in an array sorted by a key, are in the order of their canonical JSON (`bag_or_set_array_sorted`, `sortByKey_equal_keys_in_canonical_order`).
- A snapshot orders two `out` lines after one `in` line only when they travel on one channel (`ordered_same_channel`), and never two events at one time of one group that `decide` returns (`group_lines_unordered`) or of steps that no cause chain links (`independent_unordered`).

### Identity

Request ids follow the `Idempotency-Key` HTTP header (IETF).

- Each input keeps the keys of a keyed entity distinct (`send_keysDistinct`, `message_keysDistinct`).
- A reference that does not resolve is a `Fault` (`dangling_ref_reported_iff`).
- When a command arrives again with the same id and the same input, the service answers it with the first answer and does not run it again (`resent_command_gets_first_answer`).
- The service rejects a command that reuses an id with an input written differently (`reused_id_rejected`).
- When an event without `resultOf` or an answer arrives again with the same id, the service does not process it again (`redelivered_event_not_processed`, `redelivered_answer_not_processed`).
- Two values that `test` or `verify` compares equal rename into each other under the binding that the comparison ends with: each string or key as the binding pairs it, and bags and objects without repeated keys after reordering (`matchValue_renamed`, `sameRecords_renamed`). For a binding that pairs no value of domain "", this is a renaming in the sense of the theorems that follow (`matchValue_strRenamed`). The renaming is an equivalence: every value renames to itself (`renamed_refl`), a renaming read backward is the inverse binding (`renamed_symm`), and two renamings in a row are their composition, which is again one to one (`renamed_trans`, `compose_fst_nodup`, `compose_snd_nodup`). Symmetry and transitivity assume that each binding keeps a key in its entity's domain. No theorem shows that the bindings that `test` and `verify` end with pair no value of domain "" or keep keys in their domains.

### Restart

- A restart begins the service again from the part of its state that it persists: its records, its command answers, the events and answers that arrived, the requests it sent, and its created keys. It discards the part in its process memory: its instances, deadlines, awaited requests, and subscriptions (`restart_keeps`).
- A result event finds the answer to its request also when the answer arrived after a restart (`late_answer_taken`).
- A restart reads nothing of the state that it discards (`restart_forgets`).

### Comparison

- A snapshot matches a run when their lines have equal canonical JSON, whatever the order of object fields (`compareSnapshot_eq_none_iff`, `compareSnapshot_reordered`).
- A trace in which `verify` finds no violation matches its snapshot as [When a trace matches a snapshot](#when-a-trace-matches-a-snapshot) states (`compare_matches`, `contentMatch_renamed`).
- `verify` pairs the traces folder with the scenarios without a violation exactly when the folder holds only service subfolders, each file of a subfolder is a trace of an external service or is named after a scenario of its service, and each compared scenario of a service that is not external has a trace (`no_violation_iff`).
