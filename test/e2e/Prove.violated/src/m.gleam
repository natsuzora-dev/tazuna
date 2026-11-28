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
    init: Records(total: 60),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(add())],
    machines: [],
    reactions: [],
    invariants: fn(r: Records) { [#("under 50", r.total < 50)] },
    responses: [
      tazuna.response(
        name: "a big add is followed by a one",
        after: fn(e: Event) {
          case e {
            Added(n) -> n > 10
          }
        },
        then: fn(_trigger: Event, e: Event) {
          case e {
            Added(n) -> n == 1
          }
        },
        within: duration.milliseconds(5),
        deadline: fn(_r: Records, _trigger: Event) { None },
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
      steps: 5,
      explore_depth: 0,
      explore_states: 1,
      waits: [],
      values: [],
    ),
  ])
}
