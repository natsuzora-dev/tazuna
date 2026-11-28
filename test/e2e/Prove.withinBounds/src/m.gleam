import gleam/option.{None}
import tazuna.{type Ctx}
import tazuna/duration
import tazuna/table.{type Table}

pub type Records {
  Records(tasks: Table(Int, String))
}

pub type Event {
  Added(key: Int, title: String)
}

pub type Caller {
  User
}

pub type Watch {
  Watching
}

fn apply(ctx: tazuna.ApplyCtx(Records), e: Event) -> Records {
  let r = ctx.records
  case e {
    Added(k, t) -> Records(tasks: table.insert(r.tasks, k, t))
  }
}

fn add() -> tazuna.Command(Records, Event, Caller, Int, tazuna.Never) {
  tazuna.command(
    name: "add",
    callers: [tazuna.Outside(User)],
    accepts: fn(_k: Int) { [] },
    decide: fn(c: Ctx(Records, Int, Caller)) { Ok([Added(c.input, "task")]) },
    ensures: fn(_c, _r) { [] },
  )
}

/// Its table of instances has no create, so the bounds name it by the machine.
fn watch() -> tazuna.Machine(Records, Event) {
  tazuna.machine(
    name: "watch",
    instances: fn(r: Records) { table.keys(r.tasks) },
    initial: Watching,
    on: fn(_c, _e) { tazuna.Stay },
    timer: fn(_c) { None },
    effect: fn(_c) { None },
    invariants: fn(_c) { [] },
  )
}

fn tasks() -> tazuna.Service {
  tazuna.service(
    name: "tasks",
    init: Records(tasks: table.new()),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(add())],
    machines: [watch()],
    reactions: [],
    invariants: fn(r: Records) { [#("at most 2", table.size(r.tasks) <= 2)] },
    responses: [
      tazuna.response(
        name: "every task is titled",
        after: fn(_e: Event) { True },
        then: fn(_trigger: Event, e: Event) {
          case e {
            Added(_, t) -> t == "task"
          }
        },
        within: duration.milliseconds(0),
        deadline: fn(_r: Records, _trigger: Event) { None },
      ),
    ],
    cascade: 1,
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [tasks()], externals: [])
}

pub fn model() -> tazuna.Model {
  tazuna.model(spec: spec(), resource_limit: 50_000_000, scopes: [
    tazuna.scope(
      service: tasks(),
      creates: [tazuna.create(table: fn(r: Records) { r.tasks }, at_most: 2)],
      others_at_most: 1,
      steps: 5,
      explore_depth: 0,
      explore_states: 1,
      waits: [],
      values: [],
    ),
  ])
}
