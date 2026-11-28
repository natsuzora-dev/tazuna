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
    ensures: fn(c: Ctx(Records, Int, Caller), r: Records) {
      [#("grows", r.total > c.records.total)]
    },
  )
}

fn counter() -> tazuna.Service {
  tazuna.service(
    name: "counter",
    init: Records(total: 0),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(add())],
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
  tazuna.model(spec: spec(), resource_limit: 50_000_000, scopes: [])
}
