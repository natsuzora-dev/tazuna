import tazuna.{type Ctx}
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

fn apply(r: Records, e: Event) -> Records {
  case e {
    Added(k, t) -> Records(tasks: table.insert(r.tasks, k, t))
  }
}

fn add() -> tazuna.Command(Records, Event, Caller, Int, tazuna.Never) {
  tazuna.command(
    name: "add",
    callers: [User],
    accepts: fn(_k: Int) { [] },
    decide: fn(c: Ctx(Records, Int, Caller)) { Ok([Added(c.input, "task")]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn tasks() -> tazuna.Service {
  tazuna.service(
    name: "tasks",
    init: Records(tasks: table.new()),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(add())],
    machines: [],
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
        within: 0,
      ),
    ],
    bounds: tazuna.bounds(
      creates: [tazuna.create(table: fn(r: Records) { r.tasks }, at_most: 2)],
      items: 1,
      cascade: 1,
      steps: 5,
    ),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [tasks()], externals: [])
}
