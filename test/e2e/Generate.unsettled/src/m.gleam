import tazuna.{type Ctx}

pub type Records {
  Records(count: Int)
}

pub type Event {
  Added
}

pub type Caller {
  User
}

fn apply(ctx: tazuna.ApplyCtx(Records), e: Event) -> Records {
  let r = ctx.records
  case e {
    Added -> Records(count: r.count + 1)
  }
}

fn add() -> tazuna.Command(Records, Event, Caller, Nil, tazuna.Never) {
  tazuna.command(
    name: "add",
    callers: [tazuna.Outside(User)],
    accepts: fn(_n) { [] },
    decide: fn(_c: Ctx(Records, Nil, Caller)) { Ok([Added]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn counter() -> tazuna.Service {
  tazuna.service(
    name: "counter",
    init: Records(count: 0),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(add())],
    machines: [],
    reactions: [],
    invariants: fn(r: Records) { [#("not seven", r.count != 7)] },
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
