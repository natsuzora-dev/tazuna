import gleam/option.{None, Some}
import tazuna.{type Ctx, type Id}
import tazuna/bag

pub type Records {
  Records(total: Int)
}

pub type Event {
  Added(amount: Int)
  Tagged(id: Id)
  Pinged
}

pub type Caller {
  User
}

pub type Phase {
  Idle
  Waiting
  Pinging
}

fn send() -> tazuna.ExternalCommand(Int, Nil, String) {
  tazuna.external_command(external: "mail", name: "send")
}

fn apply(r: Records, e: Event) -> Records {
  case e {
    Added(n) -> Records(total: r.total + n)
    Tagged(_) | Pinged -> r
  }
}

fn add() -> tazuna.Command(Records, Event, Caller, Int, String) {
  tazuna.command(
    service: "counter",
    name: "add",
    callers: [User],
    accepts: fn(n: Int) { [#("positive", n > 0)] },
    decide: fn(c: Ctx(Records, Int, Caller)) {
      use <- tazuna.require(c.input < 100, or: "too big")
      Ok([Added(c.input), Tagged(tazuna.fresh(c.fresh, 0))])
    },
    ensures: fn(c: Ctx(Records, Int, Caller), r: Records) {
      [#("grows", r.total > c.records.total)]
    },
  )
}

fn total() -> tazuna.Query(Records, Caller, Nil, Int) {
  tazuna.query(
    service: "counter",
    name: "total",
    callers: [User],
    accepts: fn(_n) { [] },
    resolve: fn(c: Ctx(Records, Nil, Caller)) { c.records.total },
  )
}

fn watch() -> tazuna.Machine(Records, Event) {
  tazuna.machine(
    name: "watch",
    instances: fn(r: Records) {
      case r.total > 0 {
        True -> bag.from_list([0])
        False -> bag.from_list([])
      }
    },
    initial: Idle,
    on: fn(_k: Int, s: Phase, e: Event, _r: Records, _now: Int) {
      case s, e {
        Idle, Added(_) -> tazuna.Enter(Waiting)
        _, _ -> tazuna.Stay
      }
    },
    after: fn(_k: Int, s: Phase, _r: Records, _now: Int) {
      case s {
        Waiting -> Some(tazuna.Timer(after: 10, enter: Pinging))
        _ -> None
      }
    },
    effect: fn(_k: Int, s: Phase, r: Records, _now: Int) {
      case s {
        Pinging ->
          Some(
            tazuna.request_command(
              command: send(),
              input: r.total,
              on_answer: fn(a) {
                case a {
                  Ok(Nil) -> [Pinged]
                  Error(_) -> []
                }
              },
            ),
          )
        _ -> None
      }
    },
    invariants: fn(_k: Int, _s: Phase, _r: Records) { [] },
  )
}

fn counter() -> tazuna.Service {
  tazuna.service(
    name: "counter",
    init: Records(total: 0),
    apply: apply,
    subscribes: [],
    requests: [tazuna.define_command(add()), tazuna.define_query(total())],
    machines: [watch()],
    reactions: [],
    invariants: fn(r: Records) { [#("under 50", r.total < 50)] },
    responses: [],
    bounds: tazuna.bounds(creates: [], items: 3, cascade: 3, steps: 5),
  )
}

fn basic() -> tazuna.Scenario {
  tazuna.scenario(service: "counter", name: "basic", steps: [
    tazuna.step_command(command: add(), caller: User, input: 60),
  ])
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(
    services: [counter()],
    externals: [
      tazuna.external(
        name: "mail",
        commands: [tazuna.declare_command(send())],
        queries: [],
        events: [],
      ),
    ],
    scenarios: [basic()],
  )
}
