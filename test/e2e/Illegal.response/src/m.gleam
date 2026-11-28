import gleam/option.{None}
import tazuna.{type Ctx}
import tazuna/duration
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

fn tasks(name: String) -> tazuna.Service {
  tazuna.service(
    name: name,
    init: Records(tasks: table.new()),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(add())],
    machines: [],
    reactions: [],
    invariants: fn(_r) { [] },
    responses: [
      tazuna.response(
        name: "added",
        after: fn(_e: Event) { True },
        then: fn(_trigger: Event, _e: Event) { True },
        within: duration.milliseconds(-1),
        deadline: fn(_r: Records, _trigger: Event) { None },
      ),
      tazuna.response(
        name: "added",
        after: fn(_e: Event) { True },
        then: fn(_trigger: Event, _e: Event) { True },
        within: duration.milliseconds(5),
        deadline: fn(_r: Records, _trigger: Event) { None },
      ),
    ],
    cascade: 3,
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [tasks("tasks")], externals: [])
}
