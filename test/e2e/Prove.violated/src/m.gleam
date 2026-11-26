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

fn apply(r: Records, e: Event) -> Records {
  case e {
    Added(n) -> Records(total: r.total + n)
  }
}

fn add() -> tazuna.Command(Records, Event, Caller, Int, Nil) {
  tazuna.command(
    name: "add",
    callers: [User],
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
    invariants: fn(r: Records) { [#("under 50", r.total < 50)] },
    responses: [
      tazuna.response(
        name: "a big add is followed by a one",
        after: fn(e: Event) {
          case e {
            Added(n) -> n > 10
          }
        },
        then: fn(e: Event) {
          case e {
            Added(n) -> n == 1
          }
        },
        within: 5,
      ),
    ],
    bounds: tazuna.bounds(creates: [], items: 1, cascade: 1, steps: 5),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [counter()], externals: [])
}
