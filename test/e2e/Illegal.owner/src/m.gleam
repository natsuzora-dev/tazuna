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

fn send() -> tazuna.ExternalCommand(String, Nil, Nil) {
  tazuna.external_command(external: "post", name: "send")
}

fn apply(r: Records, _e: Event) -> Records {
  r
}

fn add(name: String) -> tazuna.Command(Records, Event, Caller) {
  tazuna.command(
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
    commands: [add("add")],
    queries: [],
    machines: [],
    reactions: [],
    invariants: fn(_r) { [] },
    responses: [],
    bounds: tazuna.bounds(
      creates: [tazuna.create(table: "tasks", at_most: 3)],
      items: 3,
      cascade: 10,
      steps: 5,
    ),
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [tasks("tasks")], externals: [
    tazuna.external(
      name: "mail",
      commands: [tazuna.declare_command(send())],
      queries: [],
      events: [],
    ),
  ])
}
