import tazuna.{type Ctx}

pub type Records {
  Records(a: Int, b: Int, c: Int)
}

pub type Event {
  Set(a: Int, b: Int, c: Int)
}

pub type Caller {
  User
}

fn apply(_ctx: tazuna.ApplyCtx(Records), e: Event) -> Records {
  case e {
    Set(a, b, c) -> Records(a: a, b: b, c: c)
  }
}

fn set() -> tazuna.Command(Records, Event, Caller, #(Int, Int, Int), Nil) {
  tazuna.command(
    name: "set",
    callers: [tazuna.Outside(User)],
    accepts: fn(x: #(Int, Int, Int)) {
      [#("positive", x.0 > 0 && x.1 > 0 && x.2 > 0)]
    },
    decide: fn(c: Ctx(Records, #(Int, Int, Int), Caller)) {
      Ok([Set(c.input.0, c.input.1, c.input.2)])
    },
    ensures: fn(_c, _r) { [] },
  )
}

fn cubes() -> tazuna.Service {
  tazuna.service(
    name: "cubes",
    init: Records(a: 1, b: 1, c: 1),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(set())],
    machines: [],
    reactions: [],
    invariants: fn(r: Records) {
      [#("no cube sum", r.a * r.a * r.a + r.b * r.b * r.b != r.c * r.c * r.c)]
    },
    responses: [],
    bounds: tazuna.bounds(creates: [], items: 1, cascade: 1, steps: 5),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [cubes()], externals: [])
}
