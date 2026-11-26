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

fn apply1(r: R1, e: E1) -> R1 {
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
    decide: fn(c: Ctx(R1, Int, Caller)) { Ok([Put1(c.input, 1)]) },
    ensures: fn(c: Ctx(R1, Int, Caller), r: R1) {
      [#("kept", table.get(r.items, c.input) == Some(1))]
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
    after: fn(c: tazuna.MachineCtx(Int, Phase, R1)) {
      case c.state {
        Waiting -> Some(tazuna.Timer(after: 10, enter: Pinging))
        _ -> None
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
        tazuna.send_command(
          command: bump1(),
          input: k,
          on_answer: fn(_a) { [] },
        ),
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

pub type R2 {
  R2(items: Table(Int, Int), total: Int)
}

pub type E2 {
  Put2(key: Int, value: Int)
  Del2(key: Int)
  Bumped2(amount: Int)
  Ping2
}

fn apply2(r: R2, e: E2) -> R2 {
  case e {
    Put2(k, v) -> R2(items: table.insert(r.items, k, v), total: r.total)
    Del2(k) -> R2(items: table.remove(r.items, k), total: r.total)
    Bumped2(n) -> R2(items: r.items, total: r.total + n)
    Ping2 -> r
  }
}

fn put2() -> tazuna.Command(R2, E2, Caller, Int, Nil) {
  tazuna.command(
    name: "put2",
    callers: [tazuna.Outside(User)],
    accepts: fn(k: Int) { [#("small key", k < 10)] },
    decide: fn(c: Ctx(R2, Int, Caller)) { Ok([Put2(c.input, 1)]) },
    ensures: fn(c: Ctx(R2, Int, Caller), r: R2) {
      [#("kept", table.get(r.items, c.input) == Some(1))]
    },
  )
}

fn del2() -> tazuna.Command(R2, E2, Caller, Int, Nil) {
  tazuna.command(
    name: "del2",
    callers: [tazuna.Outside(User)],
    accepts: fn(_k: Int) { [] },
    decide: fn(c: Ctx(R2, Int, Caller)) { Ok([Del2(c.input)]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn bump2() -> tazuna.Command(R2, E2, Caller, Int, Nil) {
  tazuna.command(
    name: "bump2",
    callers: [tazuna.Outside(User), tazuna.Own],
    accepts: fn(n: Int) { [#("positive", n > 0)] },
    decide: fn(c: Ctx(R2, Int, Caller)) { Ok([Bumped2(c.input)]) },
    ensures: fn(c: Ctx(R2, Int, Caller), r: R2) {
      [#("grows", r.total > c.records.total)]
    },
  )
}

fn watch2() -> tazuna.Machine(R2, E2) {
  tazuna.machine(
    name: "watch2",
    instances: fn(r: R2) { table.keys(r.items) },
    initial: Idle,
    on: fn(c: tazuna.MachineCtx(Int, Phase, R2), e: E2) {
      case c.state, e {
        Idle, Put2(k, _) if k == c.key -> tazuna.Enter(Waiting)
        _, _ -> tazuna.Stay
      }
    },
    after: fn(c: tazuna.MachineCtx(Int, Phase, R2)) {
      case c.state {
        Waiting -> Some(tazuna.Timer(after: 10, enter: Pinging))
        _ -> None
      }
    },
    effect: fn(c: tazuna.MachineCtx(Int, Phase, R2)) {
      case c.state {
        Pinging ->
          Some(
            tazuna.request_command(
              command: send(),
              input: c.key,
              on_answer: fn(a) {
                case a {
                  Ok(Nil) -> [Ping2]
                  Error(_) -> []
                }
              },
            ),
          )
        _ -> None
      }
    },
    invariants: fn(c: tazuna.MachineCtx(Int, Phase, R2)) {
      [#("key is small", c.key < 10)]
    },
  )
}

fn again2() -> tazuna.Reaction(R2, E2) {
  tazuna.reaction(name: "again2", react: fn(_c: tazuna.ReactionCtx(R2), e: E2) {
    case e {
      Put2(k, _) -> [
        tazuna.send_command(
          command: bump2(),
          input: k,
          on_answer: fn(_a) { [] },
        ),
      ]
      _ -> []
    }
  })
}

fn s2() -> tazuna.Service {
  tazuna.service(
    name: "s2",
    init: R2(items: table.new(), total: 0),
    apply: apply2,
    subscribes: [
      tazuna.subscribe(to: tick(), wrap: fn(t: Int) { Bumped2(t) }),
    ],
    declares: [
      tazuna.declare_command(put2()),
      tazuna.declare_command(del2()),
      tazuna.declare_command(bump2()),
    ],
    machines: [watch2()],
    reactions: [again2()],
    invariants: fn(r: R2) {
      [
        #("total not negative", r.total >= 0),
        #("few items", table.size(r.items) <= 2),
      ]
    },
    responses: [
      tazuna.response(
        name: "a put is pinged",
        after: fn(e: E2) {
          case e {
            Put2(_, _) -> True
            _ -> False
          }
        },
        then: fn(_trigger: E2, e: E2) {
          case e {
            Ping2 -> True
            _ -> False
          }
        },
        within: 20,
      ),
      tazuna.response(
        name: "a positive put is bumped",
        after: fn(e: E2) {
          case e {
            Put2(k, _) -> k > 0
            _ -> False
          }
        },
        then: fn(_trigger: E2, e: E2) {
          case e {
            Bumped2(_) -> True
            _ -> False
          }
        },
        within: 0,
      ),
    ],
    bounds: tazuna.bounds(
      creates: [tazuna.create(table: fn(r: R2) { r.items }, at_most: 2)],
      items: 2,
      cascade: 2,
      steps: 5,
    ),
    scenarios: [],
  )
}

pub type R3 {
  R3(items: Table(Int, Int), total: Int)
}

pub type E3 {
  Put3(key: Int, value: Int)
  Del3(key: Int)
  Bumped3(amount: Int)
  Ping3
}

fn apply3(r: R3, e: E3) -> R3 {
  case e {
    Put3(k, v) -> R3(items: table.insert(r.items, k, v), total: r.total)
    Del3(k) -> R3(items: table.remove(r.items, k), total: r.total)
    Bumped3(n) -> R3(items: r.items, total: r.total + n)
    Ping3 -> r
  }
}

fn put3() -> tazuna.Command(R3, E3, Caller, Int, Nil) {
  tazuna.command(
    name: "put3",
    callers: [tazuna.Outside(User)],
    accepts: fn(k: Int) { [#("small key", k < 10)] },
    decide: fn(c: Ctx(R3, Int, Caller)) { Ok([Put3(c.input, 1)]) },
    ensures: fn(c: Ctx(R3, Int, Caller), r: R3) {
      [#("kept", table.get(r.items, c.input) == Some(1))]
    },
  )
}

fn del3() -> tazuna.Command(R3, E3, Caller, Int, Nil) {
  tazuna.command(
    name: "del3",
    callers: [tazuna.Outside(User)],
    accepts: fn(_k: Int) { [] },
    decide: fn(c: Ctx(R3, Int, Caller)) { Ok([Del3(c.input)]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn bump3() -> tazuna.Command(R3, E3, Caller, Int, Nil) {
  tazuna.command(
    name: "bump3",
    callers: [tazuna.Outside(User), tazuna.Own],
    accepts: fn(n: Int) { [#("positive", n > 0)] },
    decide: fn(c: Ctx(R3, Int, Caller)) { Ok([Bumped3(c.input)]) },
    ensures: fn(c: Ctx(R3, Int, Caller), r: R3) {
      [#("grows", r.total > c.records.total)]
    },
  )
}

fn watch3() -> tazuna.Machine(R3, E3) {
  tazuna.machine(
    name: "watch3",
    instances: fn(r: R3) { table.keys(r.items) },
    initial: Idle,
    on: fn(c: tazuna.MachineCtx(Int, Phase, R3), e: E3) {
      case c.state, e {
        Idle, Put3(k, _) if k == c.key -> tazuna.Enter(Waiting)
        _, _ -> tazuna.Stay
      }
    },
    after: fn(c: tazuna.MachineCtx(Int, Phase, R3)) {
      case c.state {
        Waiting -> Some(tazuna.Timer(after: 10, enter: Pinging))
        _ -> None
      }
    },
    effect: fn(c: tazuna.MachineCtx(Int, Phase, R3)) {
      case c.state {
        Pinging ->
          Some(
            tazuna.request_command(
              command: send(),
              input: c.key,
              on_answer: fn(a) {
                case a {
                  Ok(Nil) -> [Ping3]
                  Error(_) -> []
                }
              },
            ),
          )
        _ -> None
      }
    },
    invariants: fn(c: tazuna.MachineCtx(Int, Phase, R3)) {
      [#("key is small", c.key < 10)]
    },
  )
}

fn again3() -> tazuna.Reaction(R3, E3) {
  tazuna.reaction(name: "again3", react: fn(_c: tazuna.ReactionCtx(R3), e: E3) {
    case e {
      Put3(k, _) -> [
        tazuna.send_command(
          command: bump3(),
          input: k,
          on_answer: fn(_a) { [] },
        ),
      ]
      _ -> []
    }
  })
}

fn s3() -> tazuna.Service {
  tazuna.service(
    name: "s3",
    init: R3(items: table.new(), total: 0),
    apply: apply3,
    subscribes: [
      tazuna.subscribe(to: tick(), wrap: fn(t: Int) { Bumped3(t) }),
    ],
    declares: [
      tazuna.declare_command(put3()),
      tazuna.declare_command(del3()),
      tazuna.declare_command(bump3()),
    ],
    machines: [watch3()],
    reactions: [again3()],
    invariants: fn(r: R3) {
      [
        #("total not negative", r.total >= 0),
        #("few items", table.size(r.items) <= 2),
      ]
    },
    responses: [
      tazuna.response(
        name: "a put is pinged",
        after: fn(e: E3) {
          case e {
            Put3(_, _) -> True
            _ -> False
          }
        },
        then: fn(_trigger: E3, e: E3) {
          case e {
            Ping3 -> True
            _ -> False
          }
        },
        within: 20,
      ),
      tazuna.response(
        name: "a positive put is bumped",
        after: fn(e: E3) {
          case e {
            Put3(k, _) -> k > 0
            _ -> False
          }
        },
        then: fn(_trigger: E3, e: E3) {
          case e {
            Bumped3(_) -> True
            _ -> False
          }
        },
        within: 0,
      ),
    ],
    bounds: tazuna.bounds(
      creates: [tazuna.create(table: fn(r: R3) { r.items }, at_most: 2)],
      items: 2,
      cascade: 2,
      steps: 5,
    ),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [s1(), s2(), s3()], externals: [
    tazuna.external(name: "mail", declares: [
      tazuna.declare_external_command(send()),
      tazuna.declare_source(tick()),
    ]),
  ])
}
