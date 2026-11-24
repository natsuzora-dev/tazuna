import tazuna.{type Ctx}
import tazuna/table.{type Table}

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
  tazuna.external_command(name: "send")
}

fn apply(r: Records, _e: Event) -> Records {
  r
}

fn add() -> tazuna.Command(Records, Event, Caller, String, Nil) {
  tazuna.command(
    name: "add",
    callers: [User],
    accepts: fn(_t: String) { [] },
    decide: fn(c: Ctx(Records, String, Caller)) { Ok([Added(c.input)]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn tasks(name: String) -> tazuna.Service {
  tazuna.service(
    name: name,
    init: Records(tasks: table.new()),
    apply: apply,
    subscribes: [],
    declares: [
      tazuna.declare_command(add()),
    ],
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
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [tasks("tasks")], externals: [
    tazuna.external(name: "mail", declares: [
      tazuna.declare_external_command(send()),
    ]),
    tazuna.external(name: "post", declares: [
      tazuna.declare_external_command(send()),
    ]),
  ])
}
