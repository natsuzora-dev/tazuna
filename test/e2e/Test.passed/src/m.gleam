import gleam/option.{None, Some}
import tazuna.{type Ctx, type Id, type QueryCtx}
import tazuna/bag

pub type Records {
  Records(total: Int, moved_at: Int)
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

fn apply(ctx: tazuna.ApplyCtx(Records), e: Event) -> Records {
  let r = ctx.records
  case e {
    Added(n) ->
      Records(total: r.total + n, moved_at: case r.total {
        0 -> ctx.now
        _ -> r.moved_at
      })
    Tagged(_) | Pinged -> r
  }
}

fn add() -> tazuna.Command(Records, Event, Caller, Int, Rejection) {
  tazuna.command(
    name: "add",
    callers: [tazuna.Outside(User)],
    accepts: fn(n: Int) { [#("positive", n > 0)] },
    decide: fn(c: Ctx(Records, Int, Caller)) {
      use <- tazuna.require(c.input < 100, or: TooBig)
      Ok([Added(c.input), Tagged(tazuna.fresh(c.fresh, 0))])
    },
    ensures: fn(c: Ctx(Records, Int, Caller), r: Records) {
      [#("grows", r.total > c.records.total)]
    },
  )
}

fn tag() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "tag",
    callers: [tazuna.Outside(User)],
    accepts: fn(_id: Id) { [] },
    decide: fn(c: Ctx(Records, Id, Caller)) { Ok([Tagged(c.input)]) },
    ensures: fn(_c: Ctx(Records, Id, Caller), _r: Records) { [] },
  )
}

fn total() -> tazuna.Query(Records, Caller, Nil, Int) {
  tazuna.query(
    name: "total",
    callers: [tazuna.Outside(User)],
    accepts: fn(_n) { [] },
    resolve: fn(c: QueryCtx(Records, Nil, Caller)) { c.records.total },
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
    timer: fn(c: tazuna.TimerCtx(Int, Phase, Records)) {
      case c.state {
        Waiting ->
          Some(tazuna.Timer(at: c.records.moved_at + 10, enter: Pinging))
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
    init: Records(total: 0, moved_at: 0),
    apply: apply,
    subscribes: [],
    declares: [
      tazuna.declare_command(add()),
      tazuna.declare_command(tag()),
      tazuna.declare_query(total()),
    ],
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
    {
      use added <- tazuna.step_command_then(
        command: add(),
        caller: User,
        input: 5,
      )
      [
        tazuna.step_command(
          command: tag(),
          caller: User,
          input: tazuna.fresh(added, 0),
        ),
      ]
    },
    tazuna.step_query(query: total(), caller: User, input: Nil),
    tazuna.step_command(command: add(), caller: User, input: 0),
    tazuna.step_command(command: add(), caller: User, input: 1),
    tazuna.step_wait(for: 10),
    tazuna.step_answer_command(
      command: send(),
      sender: tazuna.from_machine(machine: watch(), key: 0),
      with: Ok(Nil),
    ),
  ])
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [counter()], externals: [
    tazuna.external(name: "mail", declares: [
      tazuna.declare_external_command(send()),
    ]),
  ])
}
