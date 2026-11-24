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

fn stray() -> tazuna.Query(Records, Caller, Nil, Int) {
  tazuna.query(
    service: "mail",
    name: "stray",
    callers: [User],
    accepts: fn(_i) { [] },
    resolve: fn(_c) { 0 },
  )
}

fn tasks(name: String) -> tazuna.Service {
  tazuna.service(
    name: name,
    init: Records(tasks: tazuna.table_new()),
    apply: apply,
    subscribes: [],
    requests: [tazuna.define_command(add("add")), tazuna.define_query(stray())],
    machines: [],
    reactions: [],
    invariants: fn(_r) { [] },
    responses: [],
    bounds: tazuna.bounds(
      creates: [tazuna.create(table: fn(r: Records) { r.tasks }, at_most: 3)],
      items: 3,
      cascade: 10,
      steps: 5,
    ),
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(
    services: [tasks("tasks")],
    externals: [
      tazuna.external(
        name: "mail",
        commands: [tazuna.declare_command(send())],
        queries: [],
        events: [],
      ),
    ],
    scenarios: [],
  )
}
