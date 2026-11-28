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

fn send() -> tazuna.ExternalCommand(String, Nil, String) {
  tazuna.external_command(name: "send")
}

fn apply(ctx: tazuna.ApplyCtx(Records), _e: Event) -> Records {
  let r = ctx.records
  r
}

fn add() -> tazuna.Command(Records, Event, Caller, String, String) {
  tazuna.command(
    name: "add",
    callers: [tazuna.Outside(User)],
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
    cascade: 10,
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [tasks("tasks")], externals: [
    tazuna.external(name: "mail", declares: [
      tazuna.declare_external_command(send()),
    ]),
  ])
}
