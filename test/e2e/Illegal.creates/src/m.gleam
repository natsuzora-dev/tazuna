import tazuna.{type Ctx, type Table}

pub type Records {
  Records(tasks: Table(Int, String))
}

pub type Event {
  Added(title: String)
}

pub type Caller {
  User
}

fn apply(r: Records, _e: Event) -> Records {
  r
}

fn add(name: String) -> tazuna.Command(Records, Event, Caller, String, Nil) {
  tazuna.command(
    service: "tasks",
    name: name,
    callers: [User],
    accepts: fn(_t: String) { [] },
    decide: fn(c: Ctx(Records, String, Caller)) { Ok([Added(c.input)]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn tasks(name: String) -> tazuna.Service {
  tazuna.service(
    name: name,
    init: Records(tasks: tazuna.table_new()),
    apply: apply,
    subscribes: [],
    requests: [tazuna.define_command(add("add"))],
    machines: [],
    reactions: [],
    invariants: fn(_r) { [] },
    responses: [],
    bounds: tazuna.bounds(creates: [], items: 3, cascade: 10, steps: 5),
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [tasks("tasks")], externals: [])
}
