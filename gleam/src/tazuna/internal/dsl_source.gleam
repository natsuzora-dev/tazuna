//// The text of the tazuna modules in src/, which the converter reads as
//// those modules. `lake exe gen-dsl --write ..` in lean/ writes this file.

/// Each module's name, path under src/ and text.
pub const modules = [
  #(
    "tazuna",
    "tazuna.gleam",
    "//// The tazuna DSL: a spec's services, the externals they talk to, and their scenarios.
////
//// Lean gives a spec its meaning, so the bodies here only let a spec
//// compile; Gleam never runs them.
////
//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`
//// in lean/. DO NOT EDIT.

import gleam/option.{type Option}
import tazuna/bag.{type Bag}
import tazuna/duration.{type Duration}
import tazuna/instant.{type Instant}
import tazuna/internal/launch
import tazuna/table.{type Table}

/// `gleam run -m tazuna -- <command> <root> [...]` checks the spec whose
/// root module is `src/<root>.gleam`.
pub fn main() -> Nil {
  launch.main()
}

/// An identifier a step makes fresh, or one from outside the service; ids compare with `==` only. Where tazuna needs an order (machine keys), fresh ids come in the order they were made, by step and then index, before outside ids, which come by name.
pub type Id

/// The services a spec defines and the externals they talk to.
pub type Spec

/// A service: its records, the events that write them, what it reacts to, and its scenarios.
pub type Service

/// A request that may write records through events.
pub type Command(records, event, caller, input, rejection)

/// A request that answers from the records and writes nothing.
pub type Query(records, caller, input, output)

/// State kept per instance; an instance lives while its key is among the machine's instances.
pub type Machine(records, event)

/// Effects for each event, without state of its own.
pub type Reaction(records, event)

/// A service outside the spec, known by what it accepts and sends.
pub type External

/// A command an external accepts.
pub type ExternalCommand(input, output, rejection)

/// A query an external answers.
pub type ExternalQuery(input, output)

/// Events of one name that an external or a service sends.
pub type Source(event)

/// A command, query or source as its owner lists it: the service or external whose list holds it owns it. An external's list holds `Declared(Nil, Nil, Nil)`.
pub type Declared(records, event, caller)

/// A request to an external or to a command or query of the same service; its answer becomes events.
pub type Effect(event)

/// Another service's event, received as one of this service's.
pub type Subscription(event)

/// A spec with the scope prove, explore and search check it in. The scope changes which answers they can give, never what the spec means.
pub type Model

/// How far prove, explore and search look in one service: slots, run length, explore caps, values.
pub type Scope

/// The Ints and Strings `explore` tries for one input kind.
pub type Values

/// At most how many records one table of the records holds at any time.
pub type Create(records)

/// After one event, another within a time, by a deadline the records keep.
pub type Response(records, event)

/// Steps a service takes from its initial records, compared with a snapshot.
pub type Scenario(records, event, caller)

/// One step of a scenario.
pub type Step(records, event, caller)

/// What sent a request: a machine instance or a reaction.
pub type Sender

/// Where a command's new ids come from.
pub type Fresh

pub type Ctx(records, input, caller) {
  Ctx(
    records: records,
    input: input,
    caller: Origin(caller),
    now: Instant,
    fresh: Fresh,
  )
}

pub type Next(state) {
  Stay
  Enter(state)
}

/// A timer an instance waits for: a clock line at or after `at` enters the state `enter`.
pub type Timer(state) {
  Timer(at: Instant, enter: state)
}

pub type MachineCtx(key, state, records) {
  MachineCtx(key: key, state: state, records: records, now: Instant)
}

pub type ReactionCtx(records) {
  ReactionCtx(records: records, now: Instant)
}

pub type QueryCtx(records, input, caller) {
  QueryCtx(records: records, input: input, caller: Origin(caller), now: Instant)
}

/// A type with no values. As a command's rejection type it says the command never rejects: `decide` can return no `Error`, and no rejected outcome exists to reach.
pub type Never

/// Who runs a command or query: `Outside(caller)` for a request line from outside, whose `caller` is the value the line names, or `Own` for the service itself, through a machine's or reaction's `send_command` or `send_query`. A `callers` list holds origins, and `ctx.caller` is the one that ran.
pub type Origin(caller) {
  Outside(caller)
  Own
}

/// What `apply` sees: the records before the event, and the time of the step that applies it.
pub type ApplyCtx(records) {
  ApplyCtx(records: records, now: Instant)
}

/// What `timer` sees of one instance: its key and state and the records, but no time, so a timer it gives cannot move on with the clock.
pub type TimerCtx(key, state, records) {
  TimerCtx(key: key, state: state, records: records)
}

/// Named rules, as `invariants`, `accepts` and `ensures` return them: each holds or not.
pub type Rules =
  List(#(String, Bool))

/// The number of code points.
pub fn length(_string: String) -> Int {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// `use <- tazuna.require(holds, or: rejection)`: the rest of the block when it holds, else the rejection.
pub fn require(
  _holds: Bool,
  or _rejection: e,
  then _then: fn() -> Result(a, e),
) -> Result(a, e) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The spec: its services and the externals they talk to.
pub fn spec(
  services _services: List(Service),
  externals _externals: List(External),
) -> Spec {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A service. `apply` folds an event into the records: events are the only writes, so a time the records keep, such as a deadline, is written there from `ctx.now`. The service owns the commands, queries and sources it declares, and its scenarios run from `init` at time 0. `cascade` is the most internal steps one input may take: an input that needs more faults, in every command.
pub fn service(
  name _name: String,
  init _init: records,
  apply _apply: fn(ApplyCtx(records), event) -> records,
  subscribes _subscribes: List(Subscription(event)),
  declares _declares: List(Declared(records, event, caller)),
  machines _machines: List(Machine(records, event)),
  reactions _reactions: List(Reaction(records, event)),
  invariants _invariants: fn(records) -> Rules,
  responses _responses: List(Response(records, event)),
  cascade _cascade: Int,
  scenarios _scenarios: List(Scenario(records, event, caller)),
) -> Service {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A command, named by a string literal: an origin `callers` does not list or input breaking `accepts` makes it Invalid; `decide` accepts with events or rejects. `callers` lists `Outside` for each outside caller that may send it and `Own` when the service sends it itself; check rejects an empty list, `Own` with no `send_command` of it, and a `send_command` of it without `Own`. The service that lists it owns it.
pub fn command(
  name _name: String,
  callers _callers: List(Origin(caller)),
  accepts _accepts: fn(input) -> Rules,
  decide _decide: fn(Ctx(records, input, caller)) ->
    Result(List(event), rejection),
  ensures _ensures: fn(Ctx(records, input, caller), records) -> Rules,
) -> Command(records, event, caller, input, rejection) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A query, named by a string literal: it answers from the records, writes nothing and makes no ids, so `resolve` sees no source of fresh ids. `callers` works as a command's does, with `send_query`. The service that lists it owns it.
pub fn query(
  name _name: String,
  callers _callers: List(Origin(caller)),
  accepts _accepts: fn(input) -> Rules,
  resolve _resolve: fn(QueryCtx(records, input, caller)) -> output,
) -> Query(records, caller, input, output) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A machine: one instance per key in `instances`, starting at `initial` when its key appears; `on` reacts to each event with `Stay` or `Enter`. `timer` gives the timer an instance waits for, read off its state and the records: a clock line at or after the timer's `at` enters its state. `timer` sees no time, so a deadline is a time the records keep, which `apply` writes. Each entry into a state, the start included, runs `effect` once; `Stay` runs nothing, and `Enter` of the current state runs it again. A machine's instances react, start and fire in Erlang term order of their keys, so the key type is Int, String, Date, Id, Bool, an enumeration, or a tuple or one-variant record of these.
pub fn machine(
  name _name: String,
  instances _instances: fn(records) -> Bag(key),
  initial _initial: state,
  on _on: fn(MachineCtx(key, state, records), event) -> Next(state),
  timer _timer: fn(TimerCtx(key, state, records)) -> Option(Timer(state)),
  effect _effect: fn(MachineCtx(key, state, records)) -> Option(Effect(event)),
  invariants _invariants: fn(MachineCtx(key, state, records)) -> Rules,
) -> Machine(records, event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A reaction: effects for each event, without state of its own.
pub fn reaction(
  name _name: String,
  react _react: fn(ReactionCtx(records), event) -> List(Effect(event)),
) -> Reaction(records, event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// An external service: the commands, queries and sources it declares, which it owns.
pub fn external(
  name _name: String,
  declares _declares: List(Declared(Nil, Nil, Nil)),
) -> External {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A command of an external, named by a string literal. The external that lists it owns it; check requires one to.
pub fn external_command(
  name _name: String,
) -> ExternalCommand(input, output, rejection) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A query of an external, named by a string literal; `ensures` says what its answers satisfy. The external that lists it owns it; check requires one to.
pub fn external_query(
  name _name: String,
  ensures _ensures: fn(input, output) -> Rules,
) -> ExternalQuery(input, output) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// Events named `name`: the service or external that lists the source sends them.
pub fn source(name _name: String) -> Source(event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The command, for the declarations of the service that owns it.
pub fn declare_command(
  _command: Command(records, event, caller, input, rejection),
) -> Declared(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The query, for the declarations of the service that owns it.
pub fn declare_query(
  _query: Query(records, caller, input, output),
) -> Declared(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The source, for the declarations of the service or external that owns it.
pub fn declare_source(
  _source: Source(source),
) -> Declared(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The command, for the declarations of the external that owns it.
pub fn declare_external_command(
  _command: ExternalCommand(input, output, rejection),
) -> Declared(Nil, Nil, Nil) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The query, for the declarations of the external that owns it.
pub fn declare_external_query(
  _query: ExternalQuery(input, output),
) -> Declared(Nil, Nil, Nil) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// An effect: the request to an external's command, and the events its answer becomes.
pub fn request_command(
  command _command: ExternalCommand(input, output, rejection),
  input _input: input,
  on_answer _on_answer: fn(Result(output, rejection)) -> List(event),
) -> Effect(event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// An effect: the request to an external's query, and the events its answer becomes. An answer that breaks the query's `ensures` is Invalid.
pub fn request_query(
  query _query: ExternalQuery(input, output),
  input _input: input,
  on_answer _on_answer: fn(output) -> List(event),
) -> Effect(event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// An effect: the service runs its own command within the same step, as `Own`; `on_answer` gets Ok(Nil) once the command's events are applied, or its rejection.
pub fn send_command(
  command _command: Command(records, event, caller, input, rejection),
  input _input: input,
  on_answer _on_answer: fn(Result(Nil, rejection)) -> List(event),
) -> Effect(event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// An effect: the service runs its own query within the same step, as `Own`.
pub fn send_query(
  query _query: Query(records, caller, input, output),
  input _input: input,
  on_answer _on_answer: fn(output) -> List(event),
) -> Effect(event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// Receives the events of another service's or an external's source as this service's events.
pub fn subscribe(
  to _to: Source(source),
  wrap _wrap: fn(source) -> event,
) -> Subscription(event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A model: the spec, the scope prove, explore and search check each of its services in, and the solver's resource limit per question, z3's deterministic `rlimit`, which decides the same answers on every machine. A model function is a function of the root module that takes nothing and returns a `Model`; `--model <name>` picks one, and with a single one it is the one. Each line whose verdict rests on the scope names the model and the values it rests on.
pub fn model(
  spec _spec: Spec,
  scopes _scopes: List(Scope),
  resource_limit _resource_limit: Int,
) -> Model {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// How far prove, explore and search look in `service`: records per table (`creates`); items per bag and per table no create bounds (`others_at_most`), which covers bags in records and values, tables in values, each machine's table of instances and the pending requests; and inputs per run that search unrolls (`steps`, at least 1). The rest is `explore`'s, which stops after `explore_depth` inputs or once it keeps `explore_states` states, and moves the clock by each of the durations `waits` and to each deadline a state holds and the millisecond after it, and tries the Ints and Strings of `values` for an input kind's Int and String fields. prove and search name each bag and table type a bound gave slots, a machine's table by the machine.
pub fn scope(
  service _service: Service,
  creates _creates: List(Create(records)),
  others_at_most _others_at_most: Int,
  steps _steps: Int,
  explore_depth _explore_depth: Int,
  explore_states _explore_states: Int,
  waits _waits: List(Duration),
  values _values: List(Values),
) -> Scope {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The Ints and Strings `explore` tries for every Int and String field of an input of the kind `of`: a command or query the service declares, a source it subscribes to, or an external command or query whose answers it receives. A kind with no value set tries none, so its inputs with such a field are never tried.
pub fn values(
  of _of: Declared(records, event, caller),
  ints _ints: List(Int),
  strings _strings: List(String),
) -> Values {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// At most this many records in the table that `table` reads, a table field of the records, at any time.
pub fn create(
  table _table: fn(records) -> Table(k, v),
  at_most _at_most: Int,
) -> Create(records) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// After each event `trigger` satisfying `after`, an event satisfying `then(trigger, event)` within the duration `within`, the deadline included: an answer exactly `within` after the trigger is in time, one a millisecond later is not. A response that does not tie the two ignores `trigger`. `deadline` reads the deadline the records keep for a trigger while it waits for its answer, and none once it waits no more. prove checks each step against it: a trigger the step does not answer has a deadline within `within` after it, a waiting deadline ends or moves later only with its answer, and a clock line passes no waiting deadline. Together these hold the response on runs of any length.
pub fn response(
  name _name: String,
  after _after: fn(event) -> Bool,
  then _then: fn(event, event) -> Bool,
  within _within: Duration,
  deadline _deadline: fn(records, event) -> Option(Instant),
) -> Response(records, event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A scenario of the service that lists it: its steps run from the initial records at time 0, and `test` compares the trace with snapshots/<service>/<name>.jsonl.
pub fn scenario(
  name _name: String,
  steps _steps: List(Step(records, event, caller)),
) -> Scenario(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A step: the caller sends the command.
pub fn step_command(
  command _command: Command(records, event, caller, input, rejection),
  caller _caller: caller,
  input _input: input,
) -> Step(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A step: the caller sends the query. The scenario states no expected answer: `test` checks the answer as a line of the trace it compares with the snapshot.
pub fn step_query(
  query _query: Query(records, caller, input, output),
  caller _caller: caller,
  input _input: input,
) -> Step(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A step: time moves on by the duration, and the timers due fire.
pub fn step_wait(for _duration: Duration) -> Step(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A step: the external answers the one pending request to `command` that `sender` sent.
pub fn step_answer_command(
  command _command: ExternalCommand(input, output, rejection),
  sender _sender: Sender,
  with _with: Result(output, rejection),
) -> Step(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A step: the external answers the one pending request to `query` that `sender` sent.
pub fn step_answer_query(
  query _query: ExternalQuery(input, output),
  sender _sender: Sender,
  with _with: output,
) -> Step(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A step: the service receives an event of a source it subscribes to.
pub fn step_event(
  source _source: Source(source),
  value _value: source,
) -> Step(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The instance of the machine whose key is `key`, as the sender of a request.
pub fn from_machine(
  machine _machine: Machine(records, event),
  key _key: key,
) -> Sender {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The reaction, as the sender of a request.
pub fn from_reaction(reaction _reaction: Reaction(records, event)) -> Sender {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The `index`-th new id of this step: ids from different steps or indices differ.
pub fn fresh(_source: Fresh, _index: Int) -> Id {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A step: the caller sends the command, and `then` gives the steps after it. `then` receives the source of the command's new ids, so `fresh(source, index)` is the id the command made with `fresh(ctx.fresh, index)`; written with `use`, the source is a variable gleam checks.
pub fn step_command_then(
  command _command: Command(records, event, caller, input, rejection),
  caller _caller: caller,
  input _input: input,
  then _then: fn(Fresh) -> List(Step(records, event, caller)),
) -> Step(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}
",
  ),
  #(
    "tazuna/bag",
    "tazuna/bag.gleam",
    "//// Bags: multisets, whose items have no order.
////
//// Lean gives a spec its meaning, so the bodies here only let a spec
//// compile; Gleam never runs them.
////
//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`
//// in lean/. DO NOT EDIT.

/// A multiset: two bags are equal when each value occurs as often in both. Where tazuna puts values in an order the spec does not write, it uses Erlang term order, the order Gleam's Erlang target compares values in; a bag compares as the list of its items in ascending order.
pub type Bag(a)

pub type PickError {
  Empty
  Tie
}

/// A bag of the list's items.
pub fn from_list(_items: List(a)) -> Bag(a) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The bag with one more occurrence of the item.
pub fn insert(_bag: Bag(a), _item: a) -> Bag(a) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The number of items, counting each occurrence.
pub fn size(_bag: Bag(a)) -> Int {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The items that satisfy the predicate.
pub fn filter(_bag: Bag(a), keeping _keeping: fn(a) -> Bool) -> Bag(a) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// Each item transformed, occurrences kept.
pub fn map(_bag: Bag(a), with _with: fn(a) -> b) -> Bag(b) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The number of items that satisfy the predicate.
pub fn count(_bag: Bag(a), where _where: fn(a) -> Bool) -> Int {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The sum of the function over the items.
pub fn sum(_bag: Bag(a), of _of: fn(a) -> Int) -> Int {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// Whether some item satisfies the predicate.
pub fn any(_bag: Bag(a), satisfying _satisfying: fn(a) -> Bool) -> Bool {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// Whether every item satisfies the predicate.
pub fn all(_bag: Bag(a), satisfying _satisfying: fn(a) -> Bool) -> Bool {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// Whether the item occurs in the bag.
pub fn contains(_bag: Bag(a), _item: a) -> Bool {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The one item with the least key; Empty or Tie when there is not exactly one.
pub fn min_by(_bag: Bag(a), by _by: fn(a) -> Int) -> Result(a, PickError) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The one item with the greatest key; Empty or Tie when there is not exactly one.
pub fn max_by(_bag: Bag(a), by _by: fn(a) -> Int) -> Result(a, PickError) {
  panic as \"tazuna's built-ins run only in the engine\"
}
",
  ),
  #(
    "tazuna/table",
    "tazuna/table.gleam",
    "//// Tables: finite maps from keys to values.
////
//// Lean gives a spec its meaning, so the bodies here only let a spec
//// compile; Gleam never runs them.
////
//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`
//// in lean/. DO NOT EDIT.

import gleam/option.{type Option}
import tazuna/bag.{type Bag}

/// A finite map from keys to values; at most one value per key. A table in the records, a machine state, a type that crosses the wire or what a kept function captures has a plain key: Int, String, Date, Id, or a custom type or tuple of these.
pub type Table(k, v)

/// The table without keys.
pub fn new() -> Table(k, v) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A table of the pairs; a later pair replaces an earlier one's value.
pub fn from_list(_pairs: List(#(k, v))) -> Table(k, v) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The table with the key mapped to the value, replacing any value it had.
pub fn insert(_table: Table(k, v), _key: k, _value: v) -> Table(k, v) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The table without the key.
pub fn remove(_table: Table(k, v), _key: k) -> Table(k, v) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The key's value, if the table has the key.
pub fn get(_table: Table(k, v), _key: k) -> Option(v) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The number of keys.
pub fn size(_table: Table(k, v)) -> Int {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The keys.
pub fn keys(_table: Table(k, v)) -> Bag(k) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The values, one occurrence per key.
pub fn values(_table: Table(k, v)) -> Bag(v) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The entries that satisfy the predicate.
pub fn filter(
  _table: Table(k, v),
  keeping _keeping: fn(k, v) -> Bool,
) -> Table(k, v) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// Each value transformed, keys kept.
pub fn map(_table: Table(k, v), with _with: fn(k, v) -> w) -> Table(k, w) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The number of entries that satisfy the predicate.
pub fn count(_table: Table(k, v), where _where: fn(k, v) -> Bool) -> Int {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// Whether some entry satisfies the predicate.
pub fn any(
  _table: Table(k, v),
  satisfying _satisfying: fn(k, v) -> Bool,
) -> Bool {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// Whether every entry satisfies the predicate.
pub fn all(
  _table: Table(k, v),
  satisfying _satisfying: fn(k, v) -> Bool,
) -> Bool {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// `use value <- table.lookup(table, key, or: rejection)`: the rest of the block with the key's value, else the rejection.
pub fn lookup(
  _table: Table(k, v),
  _key: k,
  or _rejection: e,
  then _then: fn(v) -> Result(a, e),
) -> Result(a, e) {
  panic as \"tazuna's built-ins run only in the engine\"
}
",
  ),
  #(
    "tazuna/date",
    "tazuna/date.gleam",
    "//// Dates: days without a calendar.
////
//// Lean gives a spec its meaning, so the bodies here only let a spec
//// compile; Gleam never runs them.
////
//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`
//// in lean/. DO NOT EDIT.

/// A day. Dates have no calendar: a spec adds days and counts the days between two dates.
pub type Date

/// The date that many days later (earlier when negative).
pub fn add_days(_date: Date, _days: Int) -> Date {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The days from the first date to the second: negative when it is earlier.
pub fn days_between(from _from: Date, to _to: Date) -> Int {
  panic as \"tazuna's built-ins run only in the engine\"
}
",
  ),
  #(
    "tazuna/duration",
    "tazuna/duration.gleam",
    "//// Durations: lengths of time, each written with its unit.
////
//// Lean gives a spec its meaning, so the bodies here only let a spec
//// compile; Gleam never runs them.
////
//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`
//// in lean/. DO NOT EDIT.

/// A length of time, to the millisecond. Only `milliseconds`, `seconds`, `minutes` and `hours` make one, so every length a spec writes names its unit.
pub type Duration

/// That many milliseconds.
pub fn milliseconds(_amount: Int) -> Duration {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// That many seconds.
pub fn seconds(_amount: Int) -> Duration {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// That many minutes.
pub fn minutes(_amount: Int) -> Duration {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// That many hours.
pub fn hours(_amount: Int) -> Duration {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The duration as a number of milliseconds.
pub fn to_milliseconds(_duration: Duration) -> Int {
  panic as \"tazuna's built-ins run only in the engine\"
}
",
  ),
  #(
    "tazuna/instant",
    "tazuna/instant.gleam",
    "//// Instants: points in time a spec cannot write, only move and compare.
////
//// Lean gives a spec its meaning, so the bodies here only let a spec
//// compile; Gleam never runs them.
////
//// Generated from lean/Tazuna/Ir/Builtin.lean by `lake exe gen-dsl --write ..`
//// in lean/. DO NOT EDIT.

import tazuna/duration.{type Duration}

/// A point in time, to the millisecond. No spec can write one: it comes from a context's `now`, from an input, or from moving another by a duration, so what a spec means does not change when every instant moves by the same amount.
pub type Instant

/// The instant the duration later (earlier when it is negative).
pub fn add(_instant: Instant, _duration: Duration) -> Instant {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The duration from the first instant to the second: negative when it is earlier.
pub fn diff(from _from: Instant, to _to: Instant) -> Duration {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// Whether the first instant is earlier than the second.
pub fn is_before(_instant: Instant, _other: Instant) -> Bool {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// Whether the first instant is later than the second.
pub fn is_after(_instant: Instant, _other: Instant) -> Bool {
  panic as \"tazuna's built-ins run only in the engine\"
}
",
  ),
]

/// The functions of the modules that are built-ins; a spec calls no other.
pub const builtins = [
  "tazuna.length",
  "tazuna/bag.from_list",
  "tazuna/bag.insert",
  "tazuna/bag.size",
  "tazuna/bag.filter",
  "tazuna/bag.map",
  "tazuna/bag.count",
  "tazuna/bag.sum",
  "tazuna/bag.any",
  "tazuna/bag.all",
  "tazuna/bag.contains",
  "tazuna/bag.min_by",
  "tazuna/bag.max_by",
  "tazuna/table.new",
  "tazuna/table.from_list",
  "tazuna/table.insert",
  "tazuna/table.remove",
  "tazuna/table.get",
  "tazuna/table.size",
  "tazuna/table.keys",
  "tazuna/table.values",
  "tazuna/table.filter",
  "tazuna/table.map",
  "tazuna/table.count",
  "tazuna/table.any",
  "tazuna/table.all",
  "tazuna/date.add_days",
  "tazuna/date.days_between",
  "tazuna/duration.milliseconds",
  "tazuna/duration.seconds",
  "tazuna/duration.minutes",
  "tazuna/duration.hours",
  "tazuna/duration.to_milliseconds",
  "tazuna/instant.add",
  "tazuna/instant.diff",
  "tazuna/instant.is_before",
  "tazuna/instant.is_after",
  "tazuna.require",
  "tazuna/table.lookup",
  "tazuna.spec",
  "tazuna.service",
  "tazuna.command",
  "tazuna.query",
  "tazuna.machine",
  "tazuna.reaction",
  "tazuna.external",
  "tazuna.external_command",
  "tazuna.external_query",
  "tazuna.source",
  "tazuna.declare_command",
  "tazuna.declare_query",
  "tazuna.declare_source",
  "tazuna.declare_external_command",
  "tazuna.declare_external_query",
  "tazuna.request_command",
  "tazuna.request_query",
  "tazuna.send_command",
  "tazuna.send_query",
  "tazuna.subscribe",
  "tazuna.model",
  "tazuna.scope",
  "tazuna.values",
  "tazuna.create",
  "tazuna.response",
  "tazuna.scenario",
  "tazuna.step_command",
  "tazuna.step_query",
  "tazuna.step_wait",
  "tazuna.step_answer_command",
  "tazuna.step_answer_query",
  "tazuna.step_event",
  "tazuna.from_machine",
  "tazuna.from_reaction",
  "tazuna.fresh",
  "tazuna.step_command_then",
]

/// The built-ins whose type variables, by name, must be types `==` works on.
pub const needs_equality = [
  #("tazuna/bag.contains", ["a"]),
  #("tazuna/table.new", ["k"]),
  #("tazuna/table.from_list", ["k"]),
  #("tazuna/table.insert", ["k"]),
  #("tazuna/table.remove", ["k"]),
  #("tazuna/table.get", ["k"]),
  #("tazuna/table.lookup", ["k"]),
  #("tazuna.service", ["caller"]),
  #("tazuna.command", ["caller"]),
  #("tazuna.query", ["caller"]),
  #("tazuna.machine", ["key"]),
]

/// The function parameters built-ins keep as closure records: the
/// built-in, the parameter's position and its label.
pub const kept = [
  #("tazuna.service", 2, "apply"),
  #("tazuna.service", 7, "invariants"),
  #("tazuna.command", 2, "accepts"),
  #("tazuna.command", 3, "decide"),
  #("tazuna.command", 4, "ensures"),
  #("tazuna.query", 2, "accepts"),
  #("tazuna.query", 3, "resolve"),
  #("tazuna.machine", 1, "instances"),
  #("tazuna.machine", 3, "on"),
  #("tazuna.machine", 4, "timer"),
  #("tazuna.machine", 5, "effect"),
  #("tazuna.machine", 6, "invariants"),
  #("tazuna.reaction", 1, "react"),
  #("tazuna.external_query", 1, "ensures"),
  #("tazuna.request_command", 2, "on_answer"),
  #("tazuna.request_query", 2, "on_answer"),
  #("tazuna.send_command", 2, "on_answer"),
  #("tazuna.send_query", 2, "on_answer"),
  #("tazuna.subscribe", 1, "wrap"),
  #("tazuna.create", 0, "table"),
  #("tazuna.response", 1, "after"),
  #("tazuna.response", 2, "then"),
  #("tazuna.response", 4, "deadline"),
]

/// The types whose values are structure values, not data.
pub const structure_types = [
  "tazuna.Spec",
  "tazuna.Service",
  "tazuna.Command",
  "tazuna.Query",
  "tazuna.Machine",
  "tazuna.Reaction",
  "tazuna.External",
  "tazuna.ExternalCommand",
  "tazuna.ExternalQuery",
  "tazuna.Source",
  "tazuna.Declared",
  "tazuna.Effect",
  "tazuna.Subscription",
  "tazuna.Model",
  "tazuna.Scope",
  "tazuna.Values",
  "tazuna.Create",
  "tazuna.Response",
  "tazuna.Scenario",
  "tazuna.Step",
  "tazuna.Sender",
]
