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
import tazuna/internal/launch
import tazuna/table.{type Table}

/// `gleam run -m tazuna -- <command> <root> [...]` checks the spec whose
/// root module is `src/<root>.gleam`.
pub fn main() -> Nil {
  launch.main()
}

/// An identifier a step makes fresh, or one from outside the service; ids compare with `==` only.
pub type Id

/// The services a spec defines and the externals they talk to.
pub type Spec

/// A service: its records, the events that write them, and what it reacts to.
pub type Service

/// A request that may write records through events.
pub type Command(records, event, caller, input, rejection)

/// A request that answers from the records and writes nothing.
pub type Query(records, caller, input, output)

/// A command or query, as its service lists it.
pub type Definition(records, event, caller)

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

/// An event an external or another service sends.
pub type ExternalEvent(event)

/// An external's command, query or event, listed in its declaration.
pub type Declared

/// A request to an external or to a command or query of the same service; its answer becomes events.
pub type Effect(event)

/// Another service's event, received as one of this service's.
pub type Subscription(event)

/// How far checking goes.
pub type Bounds(records)

/// How many keys checking may add to one table of the records.
pub type Create(records)

/// After one event, another within a time.
pub type Response(event)

/// Steps a service takes from its initial records, compared with a snapshot.
pub type Scenario

/// One step of a scenario.
pub type Step(records, event, caller)

/// What sent a request: a machine instance or a reaction.
pub type Sender

/// Where a command's new ids come from.
pub type Fresh

pub type Ctx(records, input, caller) {
  Ctx(records: records, input: input, caller: caller, now: Int, fresh: Fresh)
}

pub type Next(state) {
  Stay
  Enter(state)
}

pub type Timer(state) {
  Timer(after: Int, enter: state)
}

/// A point in time, in milliseconds.
pub type Instant =
  Int

/// A length of time, in milliseconds.
pub type Duration =
  Int

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

/// The spec: its services, the externals they talk to, and scenarios of the services.
pub fn spec(
  services _services: List(Service),
  externals _externals: List(External),
  scenarios _scenarios: List(Scenario),
) -> Spec {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A service. `apply` folds an event into the records: events are the only writes.
pub fn service(
  name _name: String,
  init _init: records,
  apply _apply: fn(records, event) -> records,
  subscribes _subscribes: List(Subscription(event)),
  requests _requests: List(Definition(records, event, caller)),
  machines _machines: List(Machine(records, event)),
  reactions _reactions: List(Reaction(records, event)),
  invariants _invariants: fn(records) -> List(#(String, Bool)),
  responses _responses: List(Response(event)),
  bounds _bounds: Bounds(records),
) -> Service {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A command of the service named `service`: callers outside `callers` or input breaking `accepts` make it Invalid; `decide` accepts with events or rejects.
pub fn command(
  service _service: String,
  name _name: String,
  callers _callers: List(caller),
  accepts _accepts: fn(input) -> List(#(String, Bool)),
  decide _decide: fn(Ctx(records, input, caller)) ->
    Result(List(event), rejection),
  ensures _ensures: fn(Ctx(records, input, caller), records) ->
    List(#(String, Bool)),
) -> Command(records, event, caller, input, rejection) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A query of the service named `service`: it answers from the records and writes nothing.
pub fn query(
  service _service: String,
  name _name: String,
  callers _callers: List(caller),
  accepts _accepts: fn(input) -> List(#(String, Bool)),
  resolve _resolve: fn(Ctx(records, input, caller)) -> output,
) -> Query(records, caller, input, output) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The command, for its service's list of requests.
pub fn define_command(
  _command: Command(records, event, caller, input, rejection),
) -> Definition(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The query, for its service's list of requests.
pub fn define_query(
  _query: Query(records, caller, input, output),
) -> Definition(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A machine: one instance per key in `instances`, starting at `initial`; `on` reacts to each event, a due timer enters its state on a clock line, and entering a state may start an effect.
pub fn machine(
  name _name: String,
  instances _instances: fn(records) -> Bag(key),
  initial _initial: state,
  on _on: fn(key, state, event, records, Int) -> Next(state),
  after _after: fn(key, state, records, Int) -> Option(Timer(state)),
  effect _effect: fn(key, state, records, Int) -> Option(Effect(event)),
  invariants _invariants: fn(key, state, records) -> List(#(String, Bool)),
) -> Machine(records, event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A reaction: effects for each event, without state of its own.
pub fn reaction(
  name _name: String,
  react _react: fn(event, records, Int) -> List(Effect(event)),
) -> Reaction(records, event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// An external service and what it declares.
pub fn external(
  name _name: String,
  commands _commands: List(Declared),
  queries _queries: List(Declared),
  events _events: List(Declared),
) -> External {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A command of the external named `external`.
pub fn external_command(
  external _external: String,
  name _name: String,
) -> ExternalCommand(input, output, rejection) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A query of the external named `external`; `ensures` says what its answers satisfy.
pub fn external_query(
  external _external: String,
  name _name: String,
  ensures _ensures: fn(input, output) -> List(#(String, Bool)),
) -> ExternalQuery(input, output) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// An event of the external or service named `external`.
pub fn external_event(
  external _external: String,
  name _name: String,
) -> ExternalEvent(event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The command, for its external's declaration.
pub fn declare_command(
  _command: ExternalCommand(input, output, rejection),
) -> Declared {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The query, for its external's declaration.
pub fn declare_query(_query: ExternalQuery(input, output)) -> Declared {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// The event, for its external's declaration.
pub fn declare_event(_event: ExternalEvent(event)) -> Declared {
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

/// An effect: the service runs its own command within the same step; `on_answer` gets Ok(Nil) once the command's events are applied, or its rejection.
pub fn send_command(
  command _command: Command(records, event, caller, input, rejection),
  caller _caller: caller,
  input _input: input,
  on_answer _on_answer: fn(Result(Nil, rejection)) -> List(event),
) -> Effect(event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// An effect: the service runs its own query within the same step.
pub fn send_query(
  query _query: Query(records, caller, input, output),
  caller _caller: caller,
  input _input: input,
  on_answer _on_answer: fn(output) -> List(event),
) -> Effect(event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// Receives another service's or an external's event as one of this service's events.
pub fn subscribe(
  to _to: ExternalEvent(source),
  wrap _wrap: fn(source) -> event,
) -> Subscription(event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// How far checking goes: keys created per table, items per bag, internal steps per input, steps per run.
pub fn bounds(
  creates _creates: List(Create(records)),
  items _items: Int,
  cascade _cascade: Int,
  steps _steps: Int,
) -> Bounds(records) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// At most this many keys created in the table that `table` reads, a table field of the records.
pub fn create(
  table _table: fn(records) -> Table(k, v),
  at_most _at_most: Int,
) -> Create(records) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// After an event satisfying `after`, one satisfying `then` within `within` ms.
pub fn response(
  name _name: String,
  after _after: fn(event) -> Bool,
  then _then: fn(event) -> Bool,
  within _within: Int,
) -> Response(event) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A scenario of the service named `service`: its steps run from the initial records at time 0, and `test` compares the trace with snapshots/<service>/<name>.jsonl.
pub fn scenario(
  service _service: String,
  name _name: String,
  steps _steps: List(Step(records, event, caller)),
) -> Scenario {
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

/// A step: the caller sends the query.
pub fn step_query(
  query _query: Query(records, caller, input, output),
  caller _caller: caller,
  input _input: input,
) -> Step(records, event, caller) {
  panic as \"tazuna's built-ins run only in the engine\"
}

/// A step: time moves on by `ms`, and the timers due fire.
pub fn step_wait(ms _ms: Int) -> Step(records, event, caller) {
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

/// A step: the service receives an event it subscribes to.
pub fn step_event(
  event _event: ExternalEvent(source),
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

/// A multiset: two bags are equal when each value occurs as often in both.
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

/// A finite map from keys to values; at most one value per key.
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
  "tazuna.require",
  "tazuna/table.lookup",
  "tazuna.spec",
  "tazuna.service",
  "tazuna.command",
  "tazuna.query",
  "tazuna.define_command",
  "tazuna.define_query",
  "tazuna.machine",
  "tazuna.reaction",
  "tazuna.external",
  "tazuna.external_command",
  "tazuna.external_query",
  "tazuna.external_event",
  "tazuna.declare_command",
  "tazuna.declare_query",
  "tazuna.declare_event",
  "tazuna.request_command",
  "tazuna.request_query",
  "tazuna.send_command",
  "tazuna.send_query",
  "tazuna.subscribe",
  "tazuna.bounds",
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
