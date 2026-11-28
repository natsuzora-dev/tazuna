import tazuna.{type Ctx}

pub type Records {
  Records(rank: fn(Int) -> Int)
}

pub type Event {
  Ranked
}

pub type Caller {
  User
}

fn apply(ctx: tazuna.ApplyCtx(Records), _e: Event) -> Records {
  let r = ctx.records
  r
}

fn rank() -> tazuna.Command(Records, Event, Caller, Int, tazuna.Never) {
  tazuna.command(
    name: "rank",
    callers: [tazuna.Outside(User)],
    accepts: fn(_n: Int) { [] },
    decide: fn(_c: Ctx(Records, Int, Caller)) { Ok([Ranked]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn tasks(name: String) -> tazuna.Service {
  tazuna.service(
    name: name,
    init: Records(rank: fn(n: Int) { n }),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(rank())],
    machines: [],
    reactions: [],
    invariants: fn(_r) { [] },
    responses: [],
    cascade: 10,
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [tasks("tasks")], externals: [])
}
