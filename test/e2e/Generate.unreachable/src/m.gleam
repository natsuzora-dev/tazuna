import tazuna.{type Ctx}

pub type Records {
  Records(total: Int)
}

pub type Event {
  Added(amount: Int)
  Reset
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
    Reset -> Records(total: 0)
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
    cascade: 1,
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [counter()], externals: [])
}

pub fn model() -> tazuna.Model {
  tazuna.model(spec: spec(), resource_limit: 50_000_000, scopes: [
    tazuna.scope(
      service: counter(),
      creates: [],
      others_at_most: 1,
      steps: 3,
      explore_depth: 0,
      explore_states: 1,
      waits: [],
      values: [],
    ),
  ])
}
