import tazuna.{type Ctx}

pub type Records {
  Records(total: Int)
}

pub type Event {
  Added(amount: Int)
}

pub type Caller {
  User
}

pub type Rejection {
  Negative
}

fn apply(ctx: tazuna.ApplyCtx(Records), e: Event) -> Records {
  let r = ctx.records
  case e {
    Added(n) -> Records(total: r.total + n)
  }
}

fn add() -> tazuna.Command(Records, Event, Caller, Int, tazuna.Never) {
  tazuna.command(
    name: "add",
    callers: [tazuna.Outside(User)],
    accepts: fn(n: Int) { [#("positive", n > 0)] },
    decide: fn(c: Ctx(Records, Int, Caller)) { Ok([Added(c.input)]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn check() -> tazuna.Command(Records, Event, Caller, Nil, Rejection) {
  tazuna.command(
    name: "check",
    callers: [tazuna.Outside(User)],
    accepts: fn(_n) { [] },
    decide: fn(c: Ctx(Records, Nil, Caller)) {
      use <- tazuna.require(c.records.total >= 0, Negative)
      Ok([])
    },
    ensures: fn(_c, _r) { [] },
  )
}

fn counter() -> tazuna.Service {
  tazuna.service(
    name: "counter",
    init: Records(total: 0),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(add()), tazuna.declare_command(check())],
    machines: [],
    reactions: [],
    invariants: fn(r: Records) { [#("not negative", r.total >= 0)] },
    responses: [],
    bounds: tazuna.bounds(creates: [], items: 1, cascade: 1, steps: 3),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [counter()], externals: [])
}
