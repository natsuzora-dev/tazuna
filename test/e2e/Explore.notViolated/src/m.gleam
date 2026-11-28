import gleam/option.{None}
import tazuna.{type Ctx}
import tazuna/duration

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
  case e {
    Added(n) -> Records(total: ctx.records.total + n)
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
    invariants: fn(r: Records) { [#("not seven", r.total != 7)] },
    responses: [
      tazuna.response(
        name: "acknowledged",
        after: fn(_e: Event) { True },
        then: fn(_t: Event, _e: Event) { False },
        within: duration.milliseconds(1),
        deadline: fn(_r: Records, _e: Event) { None },
      ),
    ],
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
      explore_depth: 3,
      explore_states: 100,
      waits: [duration.milliseconds(5)],
      values: [
        tazuna.values(of: tazuna.declare_command(add()), ints: [1], strings: []),
      ],
    ),
  ])
}
