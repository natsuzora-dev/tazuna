import gleam/option.{type Option, None, Some}
import tazuna.{type Ctx, type Id, type QueryCtx}
import tazuna/bag

pub type Records {
  Records(total: Int, first: Option(Id), moved_at: Int)
}

pub type Event {
  Added(amount: Int)
  Tagged(id: Id)
  Made(id: Id)
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
  case e, r.first {
    Added(n), _ ->
      Records(..r, total: r.total + n, moved_at: case r.total {
        0 -> ctx.now
        _ -> r.moved_at
      })
    Made(id), None -> Records(..r, first: Some(id))
    Made(_), Some(_) | Tagged(_), _ | Pinged, _ -> r
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

fn pair() -> tazuna.Command(Records, Event, Caller, Nil, Rejection) {
  tazuna.command(
    name: "pair",
    callers: [tazuna.Outside(User)],
    accepts: fn(_n) { [] },
    decide: fn(c: Ctx(Records, Nil, Caller)) {
      Ok([Made(tazuna.fresh(c.fresh, 0)), Made(tazuna.fresh(c.fresh, 1))])
    },
    ensures: fn(_c: Ctx(Records, Nil, Caller), _r: Records) { [] },
  )
}

fn is_first() -> tazuna.Query(Records, Caller, Id, Bool) {
  tazuna.query(
    name: "is_first",
    callers: [tazuna.Outside(User)],
    accepts: fn(_n) { [] },
    resolve: fn(c: QueryCtx(Records, Id, Caller)) {
      c.records.first == Some(c.input)
    },
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
    init: Records(total: 0, first: None, moved_at: 0),
    apply: apply,
    subscribes: [],
    declares: [
      tazuna.declare_command(add()),
      tazuna.declare_query(total()),
      tazuna.declare_command(pair()),
      tazuna.declare_query(is_first()),
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
    tazuna.step_command(command: add(), caller: User, input: 5),
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
