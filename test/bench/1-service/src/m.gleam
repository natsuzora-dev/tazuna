import gleam/option.{None, Some}
import tazuna.{type Ctx}
import tazuna/bag
import tazuna/table.{type Table}

pub type Caller {
  User
}

pub type Phase {
  Idle
  Waiting
  Pinging
}

fn send() -> tazuna.ExternalCommand(Int, Nil, Nil) {
  tazuna.external_command(name: "send")
}

fn tick() -> tazuna.Source(Int) {
  tazuna.source(name: "tick")
}

pub type R1 {
  R1(items: Table(Int, Int), total: Int)
}

pub type E1 {
  Put1(key: Int, value: Int)
  Del1(key: Int)
  Bumped1(amount: Int)
  Ping1
}

fn apply1(ctx: tazuna.ApplyCtx(R1), e: E1) -> R1 {
  let r = ctx.records
  case e {
    Put1(k, v) -> R1(items: table.insert(r.items, k, v), total: r.total)
    Del1(k) -> R1(items: table.remove(r.items, k), total: r.total)
    Bumped1(n) -> R1(items: r.items, total: r.total + n)
    Ping1 -> r
  }
}

fn put1() -> tazuna.Command(R1, E1, Caller, Int, Nil) {
  tazuna.command(
    name: "put1",
    callers: [tazuna.Outside(User)],
    accepts: fn(k: Int) { [#("small key", k < 10)] },
    decide: fn(c: Ctx(R1, Int, Caller)) { Ok([Put1(c.input, c.now + 10)]) },
    ensures: fn(c: Ctx(R1, Int, Caller), r: R1) {
      [#("kept", table.get(r.items, c.input) == Some(c.now + 10))]
    },
  )
}

fn del1() -> tazuna.Command(R1, E1, Caller, Int, Nil) {
  tazuna.command(
    name: "del1",
    callers: [tazuna.Outside(User)],
    accepts: fn(_k: Int) { [] },
    decide: fn(c: Ctx(R1, Int, Caller)) { Ok([Del1(c.input)]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn bump1() -> tazuna.Command(R1, E1, Caller, Int, Nil) {
  tazuna.command(
    name: "bump1",
    callers: [tazuna.Outside(User), tazuna.Own],
    accepts: fn(n: Int) { [#("positive", n > 0)] },
    decide: fn(c: Ctx(R1, Int, Caller)) { Ok([Bumped1(c.input)]) },
    ensures: fn(c: Ctx(R1, Int, Caller), r: R1) {
      [#("grows", r.total > c.records.total)]
    },
  )
}

fn watch1() -> tazuna.Machine(R1, E1) {
  tazuna.machine(
    name: "watch1",
    instances: fn(r: R1) { table.keys(r.items) },
    initial: Idle,
    on: fn(c: tazuna.MachineCtx(Int, Phase, R1), e: E1) {
      case c.state, e {
        Idle, Put1(k, _) if k == c.key -> tazuna.Enter(Waiting)
        _, _ -> tazuna.Stay
      }
    },
    timer: fn(c: tazuna.TimerCtx(Int, Phase, R1)) {
      case c.state, table.get(c.records.items, c.key) {
        Waiting, Some(at) -> Some(tazuna.Timer(at: at, enter: Pinging))
        _, _ -> None
      }
    },
    effect: fn(c: tazuna.MachineCtx(Int, Phase, R1)) {
      case c.state {
        Pinging ->
          Some(
            tazuna.request_command(
              command: send(),
              input: c.key,
              on_answer: fn(a) {
                case a {
                  Ok(Nil) -> [Ping1]
                  Error(_) -> []
                }
              },
            ),
          )
        _ -> None
      }
    },
    invariants: fn(c: tazuna.MachineCtx(Int, Phase, R1)) {
      [#("key is small", c.key < 10)]
    },
  )
}

fn again1() -> tazuna.Reaction(R1, E1) {
  tazuna.reaction(name: "again1", react: fn(_c: tazuna.ReactionCtx(R1), e: E1) {
    case e {
      Put1(k, _) -> [
        tazuna.send_command(command: bump1(), input: k, on_answer: fn(_a) { [] }),
      ]
      _ -> []
    }
  })
}

fn s1() -> tazuna.Service {
  tazuna.service(
    name: "s1",
    init: R1(items: table.new(), total: 0),
    apply: apply1,
    subscribes: [
      tazuna.subscribe(to: tick(), wrap: fn(t: Int) { Bumped1(t) }),
    ],
    declares: [
      tazuna.declare_command(put1()),
      tazuna.declare_command(del1()),
      tazuna.declare_command(bump1()),
    ],
    machines: [watch1()],
    reactions: [again1()],
    invariants: fn(r: R1) {
      [
        #("total not negative", r.total >= 0),
        #("few items", table.size(r.items) <= 2),
      ]
    },
    responses: [
      tazuna.response(
        name: "a put is pinged",
        after: fn(e: E1) {
          case e {
            Put1(_, _) -> True
            _ -> False
          }
        },
        then: fn(_trigger: E1, e: E1) {
          case e {
            Ping1 -> True
            _ -> False
          }
        },
        within: 20,
      ),
      tazuna.response(
        name: "a positive put is bumped",
        after: fn(e: E1) {
          case e {
            Put1(k, _) -> k > 0
            _ -> False
          }
        },
        then: fn(_trigger: E1, e: E1) {
          case e {
            Bumped1(_) -> True
            _ -> False
          }
        },
        within: 0,
      ),
    ],
    bounds: tazuna.bounds(
      creates: [tazuna.create(table: fn(r: R1) { r.items }, at_most: 2)],
      items: 2,
      cascade: 2,
      steps: 5,
    ),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [s1()], externals: [
    tazuna.external(name: "mail", declares: [
      tazuna.declare_external_command(send()),
      tazuna.declare_source(tick()),
    ]),
  ])
}
