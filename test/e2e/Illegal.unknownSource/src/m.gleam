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

fn apply(ctx: tazuna.ApplyCtx(Records), _e: Event) -> Records {
  let r = ctx.records
  r
}

fn add() -> tazuna.Command(Records, Event, Caller, String, tazuna.Never) {
  tazuna.command(
    name: "add",
    callers: [tazuna.Outside(User)],
    accepts: fn(_t: String) { [] },
    decide: fn(c: Ctx(Records, String, Caller)) { Ok([Added(c.input)]) },
    ensures: fn(_c, _r) { [] },
  )
}

/// The clock's ticks carry the time; the subscription below reads them as text.
fn tick() -> tazuna.Source(Int) {
  tazuna.source(name: "tick")
}

fn tasks(name: String) -> tazuna.Service {
  tazuna.service(
    name: name,
    init: Records(tasks: table.new()),
    apply: apply,
    subscribes: [
      tazuna.subscribe(to: tazuna.source(name: "tick"), wrap: fn(t: String) {
        Added(t)
      }),
    ],
    declares: [tazuna.declare_command(add())],
    machines: [],
    reactions: [],
    invariants: fn(_r) { [] },
    responses: [],
    bounds: tazuna.bounds(
      creates: [tazuna.create(table: fn(r: Records) { r.tasks }, at_most: 3)],
      others_at_most: 3,
      cascade: 10,
      steps: 5,
    ),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [tasks("tasks")], externals: [
    tazuna.external(name: "clock", declares: [tazuna.declare_source(tick())]),
  ])
}
