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

pub type Rejection {
  TooBig
}

pub type Phase {
  Idle
  Waiting
  Pinging
}

fn send() -> tazuna.ExternalCommand(Int, Nil, Nil) {
  tazuna.external_command(name: "send")
}

fn apply(r: Records, e: Event) -> Records {
  case e {
    Added(n) -> Records(total: r.total + n)
    Tagged(_) | Pinged -> r
  }
}

fn add() -> tazuna.Command(Records, Event, Caller, Int, Rejection) {
  tazuna.command(
    name: "add",
    callers: [User],
    accepts: fn(n: Int) { [#("positive", n > 0)] },
    decide: fn(c: Ctx(Records, Int, Caller)) {
      use <- tazuna.require(c.input < 100, or: TooBig)
      Ok([Added(c.input), Tagged(tazuna.fresh(c.fresh, 0))])
    },
    ensures: fn(c: Ctx(Records, Int, Caller), r: Records) {
      [#("grows", r.total > c.records.total + 1)]
    },
  )
}

fn total() -> tazuna.Query(Records, Caller, Nil, Int) {
  tazuna.query(
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
    on: fn(c: tazuna.MachineCtx(Int, Phase, Records), e: Event) {
      case c.state, e {
        Idle, Added(_) -> tazuna.Enter(Waiting)
        _, _ -> tazuna.Stay
      }
    },
    after: fn(c: tazuna.MachineCtx(Int, Phase, Records)) {
      case c.state {
        Waiting -> Some(tazuna.Timer(after: 10, enter: Pinging))
        _ -> None
      }
    },
    effect: fn(c: tazuna.MachineCtx(Int, Phase, Records)) {
      case c.state {
        Pinging ->
          Some(
            tazuna.request_command(
              command: send(),
              input: c.records.total,
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
    invariants: fn(_c: tazuna.MachineCtx(Int, Phase, Records)) { [] },
  )
}

fn counter() -> tazuna.Service {
  tazuna.service(
    name: "counter",
    init: Records(total: 0),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(add()), tazuna.declare_query(total())],
    machines: [watch()],
    reactions: [],
    invariants: fn(r: Records) { [#("under 50", r.total < 50)] },
    responses: [],
    bounds: tazuna.bounds(creates: [], items: 3, cascade: 3, steps: 5),
    scenarios: [basic()],
  )
}

fn basic() -> tazuna.Scenario(Records, Event, Caller) {
  tazuna.scenario(name: "basic", steps: [
    tazuna.step_command(command: add(), caller: User, input: 1),
  ])
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [counter()], externals: [
    tazuna.external(name: "mail", declares: [
      tazuna.declare_external_command(send()),
    ]),
  ])
}
