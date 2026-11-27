import tazuna.{type Ctx}

pub type Records {
  Records(n: Int)
}

pub type Event {
  Labelled(tag: Int)
}

pub type Caller {
  User
}

fn apply(ctx: tazuna.ApplyCtx(Records), e: Event) -> Records {
  let r = ctx.records
  case e {
    Labelled(_) -> Records(n: r.n + 1)
  }
}

fn label() -> tazuna.Command(Records, Event, Caller, Int, tazuna.Never) {
  tazuna.command(
    name: "label",
    callers: [tazuna.Outside(User)],
    accepts: fn(_n: Int) { [] },
    decide: fn(c: Ctx(Records, Int, Caller)) { Ok([Labelled(tag: c.input)]) },
    ensures: fn(_c: Ctx(Records, Int, Caller), _r: Records) { [] },
  )
}

fn svc() -> tazuna.Service {
  tazuna.service(
    name: "tags",
    init: Records(n: 0),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(label())],
    machines: [],
    reactions: [],
    invariants: fn(_r: Records) { [] },
    responses: [],
    bounds: tazuna.bounds(creates: [], others_at_most: 1, cascade: 1, steps: 1),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [svc()], externals: [])
}
