import gleam/option.{None, Some}
import tazuna.{type Ctx}
import tazuna/bag
import tazuna/instant.{type Instant}
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
  R1(items: Table(Int, Instant), total: Int)
}

pub type E1 {
  Put1(key: Int, value: Instant)
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
    decide: fn(c: Ctx(R1, Int, Caller)) {
      Ok([Put1(c.input, instant.add(c.now, 10))])
    },
    ensures: fn(c: Ctx(R1, Int, Caller), r: R1) {
      [#("kept", table.get(r.items, c.input) == Some(instant.add(c.now, 10)))]
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
        deadline: fn(r: R1, trigger: E1) {
          case trigger {
            Put1(k, _) -> table.get(r.items, k)
            _ -> None
          }
        },
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
        deadline: fn(_r: R1, _trigger: E1) { None },
      ),
    ],
    cascade: 2,
    scenarios: [],
  )
}

pub type R2 {
  R2(items: Table(Int, Instant), total: Int)
}

pub type E2 {
  Put2(key: Int, value: Instant)
  Del2(key: Int)
  Bumped2(amount: Int)
  Ping2
}

fn apply2(ctx: tazuna.ApplyCtx(R2), e: E2) -> R2 {
  let r = ctx.records
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
    decide: fn(c: Ctx(R2, Int, Caller)) {
      Ok([Put2(c.input, instant.add(c.now, 10))])
    },
    ensures: fn(c: Ctx(R2, Int, Caller), r: R2) {
      [#("kept", table.get(r.items, c.input) == Some(instant.add(c.now, 10)))]
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
    timer: fn(c: tazuna.TimerCtx(Int, Phase, R2)) {
      case c.state, table.get(c.records.items, c.key) {
        Waiting, Some(at) -> Some(tazuna.Timer(at: at, enter: Pinging))
        _, _ -> None
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
        tazuna.send_command(command: bump2(), input: k, on_answer: fn(_a) { [] }),
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
        deadline: fn(r: R2, trigger: E2) {
          case trigger {
            Put2(k, _) -> table.get(r.items, k)
            _ -> None
          }
        },
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
        deadline: fn(_r: R2, _trigger: E2) { None },
      ),
    ],
    cascade: 2,
    scenarios: [],
  )
}

pub type R3 {
  R3(items: Table(Int, Instant), total: Int)
}

pub type E3 {
  Put3(key: Int, value: Instant)
  Del3(key: Int)
  Bumped3(amount: Int)
  Ping3
}

fn apply3(ctx: tazuna.ApplyCtx(R3), e: E3) -> R3 {
  let r = ctx.records
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
    decide: fn(c: Ctx(R3, Int, Caller)) {
      Ok([Put3(c.input, instant.add(c.now, 10))])
    },
    ensures: fn(c: Ctx(R3, Int, Caller), r: R3) {
      [#("kept", table.get(r.items, c.input) == Some(instant.add(c.now, 10)))]
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
    timer: fn(c: tazuna.TimerCtx(Int, Phase, R3)) {
      case c.state, table.get(c.records.items, c.key) {
        Waiting, Some(at) -> Some(tazuna.Timer(at: at, enter: Pinging))
        _, _ -> None
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
        tazuna.send_command(command: bump3(), input: k, on_answer: fn(_a) { [] }),
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
        deadline: fn(r: R3, trigger: E3) {
          case trigger {
            Put3(k, _) -> table.get(r.items, k)
            _ -> None
          }
        },
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
        deadline: fn(_r: R3, _trigger: E3) { None },
      ),
    ],
    cascade: 2,
    scenarios: [],
  )
}

pub type R4 {
  R4(items: Table(Int, Instant), total: Int)
}

pub type E4 {
  Put4(key: Int, value: Instant)
  Del4(key: Int)
  Bumped4(amount: Int)
  Ping4
}

fn apply4(ctx: tazuna.ApplyCtx(R4), e: E4) -> R4 {
  let r = ctx.records
  case e {
    Put4(k, v) -> R4(items: table.insert(r.items, k, v), total: r.total)
    Del4(k) -> R4(items: table.remove(r.items, k), total: r.total)
    Bumped4(n) -> R4(items: r.items, total: r.total + n)
    Ping4 -> r
  }
}

fn put4() -> tazuna.Command(R4, E4, Caller, Int, Nil) {
  tazuna.command(
    name: "put4",
    callers: [tazuna.Outside(User)],
    accepts: fn(k: Int) { [#("small key", k < 10)] },
    decide: fn(c: Ctx(R4, Int, Caller)) {
      Ok([Put4(c.input, instant.add(c.now, 10))])
    },
    ensures: fn(c: Ctx(R4, Int, Caller), r: R4) {
      [#("kept", table.get(r.items, c.input) == Some(instant.add(c.now, 10)))]
    },
  )
}

fn del4() -> tazuna.Command(R4, E4, Caller, Int, Nil) {
  tazuna.command(
    name: "del4",
    callers: [tazuna.Outside(User)],
    accepts: fn(_k: Int) { [] },
    decide: fn(c: Ctx(R4, Int, Caller)) { Ok([Del4(c.input)]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn bump4() -> tazuna.Command(R4, E4, Caller, Int, Nil) {
  tazuna.command(
    name: "bump4",
    callers: [tazuna.Outside(User), tazuna.Own],
    accepts: fn(n: Int) { [#("positive", n > 0)] },
    decide: fn(c: Ctx(R4, Int, Caller)) { Ok([Bumped4(c.input)]) },
    ensures: fn(c: Ctx(R4, Int, Caller), r: R4) {
      [#("grows", r.total > c.records.total)]
    },
  )
}

fn watch4() -> tazuna.Machine(R4, E4) {
  tazuna.machine(
    name: "watch4",
    instances: fn(r: R4) { table.keys(r.items) },
    initial: Idle,
    on: fn(c: tazuna.MachineCtx(Int, Phase, R4), e: E4) {
      case c.state, e {
        Idle, Put4(k, _) if k == c.key -> tazuna.Enter(Waiting)
        _, _ -> tazuna.Stay
      }
    },
    timer: fn(c: tazuna.TimerCtx(Int, Phase, R4)) {
      case c.state, table.get(c.records.items, c.key) {
        Waiting, Some(at) -> Some(tazuna.Timer(at: at, enter: Pinging))
        _, _ -> None
      }
    },
    effect: fn(c: tazuna.MachineCtx(Int, Phase, R4)) {
      case c.state {
        Pinging ->
          Some(
            tazuna.request_command(
              command: send(),
              input: c.key,
              on_answer: fn(a) {
                case a {
                  Ok(Nil) -> [Ping4]
                  Error(_) -> []
                }
              },
            ),
          )
        _ -> None
      }
    },
    invariants: fn(c: tazuna.MachineCtx(Int, Phase, R4)) {
      [#("key is small", c.key < 10)]
    },
  )
}

fn again4() -> tazuna.Reaction(R4, E4) {
  tazuna.reaction(name: "again4", react: fn(_c: tazuna.ReactionCtx(R4), e: E4) {
    case e {
      Put4(k, _) -> [
        tazuna.send_command(command: bump4(), input: k, on_answer: fn(_a) { [] }),
      ]
      _ -> []
    }
  })
}

fn s4() -> tazuna.Service {
  tazuna.service(
    name: "s4",
    init: R4(items: table.new(), total: 0),
    apply: apply4,
    subscribes: [
      tazuna.subscribe(to: tick(), wrap: fn(t: Int) { Bumped4(t) }),
    ],
    declares: [
      tazuna.declare_command(put4()),
      tazuna.declare_command(del4()),
      tazuna.declare_command(bump4()),
    ],
    machines: [watch4()],
    reactions: [again4()],
    invariants: fn(r: R4) {
      [
        #("total not negative", r.total >= 0),
        #("few items", table.size(r.items) <= 2),
      ]
    },
    responses: [
      tazuna.response(
        name: "a put is pinged",
        after: fn(e: E4) {
          case e {
            Put4(_, _) -> True
            _ -> False
          }
        },
        then: fn(_trigger: E4, e: E4) {
          case e {
            Ping4 -> True
            _ -> False
          }
        },
        within: 20,
        deadline: fn(r: R4, trigger: E4) {
          case trigger {
            Put4(k, _) -> table.get(r.items, k)
            _ -> None
          }
        },
      ),
      tazuna.response(
        name: "a positive put is bumped",
        after: fn(e: E4) {
          case e {
            Put4(k, _) -> k > 0
            _ -> False
          }
        },
        then: fn(_trigger: E4, e: E4) {
          case e {
            Bumped4(_) -> True
            _ -> False
          }
        },
        within: 0,
        deadline: fn(_r: R4, _trigger: E4) { None },
      ),
    ],
    cascade: 2,
    scenarios: [],
  )
}

pub type R5 {
  R5(items: Table(Int, Instant), total: Int)
}

pub type E5 {
  Put5(key: Int, value: Instant)
  Del5(key: Int)
  Bumped5(amount: Int)
  Ping5
}

fn apply5(ctx: tazuna.ApplyCtx(R5), e: E5) -> R5 {
  let r = ctx.records
  case e {
    Put5(k, v) -> R5(items: table.insert(r.items, k, v), total: r.total)
    Del5(k) -> R5(items: table.remove(r.items, k), total: r.total)
    Bumped5(n) -> R5(items: r.items, total: r.total + n)
    Ping5 -> r
  }
}

fn put5() -> tazuna.Command(R5, E5, Caller, Int, Nil) {
  tazuna.command(
    name: "put5",
    callers: [tazuna.Outside(User)],
    accepts: fn(k: Int) { [#("small key", k < 10)] },
    decide: fn(c: Ctx(R5, Int, Caller)) {
      Ok([Put5(c.input, instant.add(c.now, 10))])
    },
    ensures: fn(c: Ctx(R5, Int, Caller), r: R5) {
      [#("kept", table.get(r.items, c.input) == Some(instant.add(c.now, 10)))]
    },
  )
}

fn del5() -> tazuna.Command(R5, E5, Caller, Int, Nil) {
  tazuna.command(
    name: "del5",
    callers: [tazuna.Outside(User)],
    accepts: fn(_k: Int) { [] },
    decide: fn(c: Ctx(R5, Int, Caller)) { Ok([Del5(c.input)]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn bump5() -> tazuna.Command(R5, E5, Caller, Int, Nil) {
  tazuna.command(
    name: "bump5",
    callers: [tazuna.Outside(User), tazuna.Own],
    accepts: fn(n: Int) { [#("positive", n > 0)] },
    decide: fn(c: Ctx(R5, Int, Caller)) { Ok([Bumped5(c.input)]) },
    ensures: fn(c: Ctx(R5, Int, Caller), r: R5) {
      [#("grows", r.total > c.records.total)]
    },
  )
}

fn watch5() -> tazuna.Machine(R5, E5) {
  tazuna.machine(
    name: "watch5",
    instances: fn(r: R5) { table.keys(r.items) },
    initial: Idle,
    on: fn(c: tazuna.MachineCtx(Int, Phase, R5), e: E5) {
      case c.state, e {
        Idle, Put5(k, _) if k == c.key -> tazuna.Enter(Waiting)
        _, _ -> tazuna.Stay
      }
    },
    timer: fn(c: tazuna.TimerCtx(Int, Phase, R5)) {
      case c.state, table.get(c.records.items, c.key) {
        Waiting, Some(at) -> Some(tazuna.Timer(at: at, enter: Pinging))
        _, _ -> None
      }
    },
    effect: fn(c: tazuna.MachineCtx(Int, Phase, R5)) {
      case c.state {
        Pinging ->
          Some(
            tazuna.request_command(
              command: send(),
              input: c.key,
              on_answer: fn(a) {
                case a {
                  Ok(Nil) -> [Ping5]
                  Error(_) -> []
                }
              },
            ),
          )
        _ -> None
      }
    },
    invariants: fn(c: tazuna.MachineCtx(Int, Phase, R5)) {
      [#("key is small", c.key < 10)]
    },
  )
}

fn again5() -> tazuna.Reaction(R5, E5) {
  tazuna.reaction(name: "again5", react: fn(_c: tazuna.ReactionCtx(R5), e: E5) {
    case e {
      Put5(k, _) -> [
        tazuna.send_command(command: bump5(), input: k, on_answer: fn(_a) { [] }),
      ]
      _ -> []
    }
  })
}

fn s5() -> tazuna.Service {
  tazuna.service(
    name: "s5",
    init: R5(items: table.new(), total: 0),
    apply: apply5,
    subscribes: [
      tazuna.subscribe(to: tick(), wrap: fn(t: Int) { Bumped5(t) }),
    ],
    declares: [
      tazuna.declare_command(put5()),
      tazuna.declare_command(del5()),
      tazuna.declare_command(bump5()),
    ],
    machines: [watch5()],
    reactions: [again5()],
    invariants: fn(r: R5) {
      [
        #("total not negative", r.total >= 0),
        #("few items", table.size(r.items) <= 2),
      ]
    },
    responses: [
      tazuna.response(
        name: "a put is pinged",
        after: fn(e: E5) {
          case e {
            Put5(_, _) -> True
            _ -> False
          }
        },
        then: fn(_trigger: E5, e: E5) {
          case e {
            Ping5 -> True
            _ -> False
          }
        },
        within: 20,
        deadline: fn(r: R5, trigger: E5) {
          case trigger {
            Put5(k, _) -> table.get(r.items, k)
            _ -> None
          }
        },
      ),
      tazuna.response(
        name: "a positive put is bumped",
        after: fn(e: E5) {
          case e {
            Put5(k, _) -> k > 0
            _ -> False
          }
        },
        then: fn(_trigger: E5, e: E5) {
          case e {
            Bumped5(_) -> True
            _ -> False
          }
        },
        within: 0,
        deadline: fn(_r: R5, _trigger: E5) { None },
      ),
    ],
    cascade: 2,
    scenarios: [],
  )
}

pub type R6 {
  R6(items: Table(Int, Instant), total: Int)
}

pub type E6 {
  Put6(key: Int, value: Instant)
  Del6(key: Int)
  Bumped6(amount: Int)
  Ping6
}

fn apply6(ctx: tazuna.ApplyCtx(R6), e: E6) -> R6 {
  let r = ctx.records
  case e {
    Put6(k, v) -> R6(items: table.insert(r.items, k, v), total: r.total)
    Del6(k) -> R6(items: table.remove(r.items, k), total: r.total)
    Bumped6(n) -> R6(items: r.items, total: r.total + n)
    Ping6 -> r
  }
}

fn put6() -> tazuna.Command(R6, E6, Caller, Int, Nil) {
  tazuna.command(
    name: "put6",
    callers: [tazuna.Outside(User)],
    accepts: fn(k: Int) { [#("small key", k < 10)] },
    decide: fn(c: Ctx(R6, Int, Caller)) {
      Ok([Put6(c.input, instant.add(c.now, 10))])
    },
    ensures: fn(c: Ctx(R6, Int, Caller), r: R6) {
      [#("kept", table.get(r.items, c.input) == Some(instant.add(c.now, 10)))]
    },
  )
}

fn del6() -> tazuna.Command(R6, E6, Caller, Int, Nil) {
  tazuna.command(
    name: "del6",
    callers: [tazuna.Outside(User)],
    accepts: fn(_k: Int) { [] },
    decide: fn(c: Ctx(R6, Int, Caller)) { Ok([Del6(c.input)]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn bump6() -> tazuna.Command(R6, E6, Caller, Int, Nil) {
  tazuna.command(
    name: "bump6",
    callers: [tazuna.Outside(User), tazuna.Own],
    accepts: fn(n: Int) { [#("positive", n > 0)] },
    decide: fn(c: Ctx(R6, Int, Caller)) { Ok([Bumped6(c.input)]) },
    ensures: fn(c: Ctx(R6, Int, Caller), r: R6) {
      [#("grows", r.total > c.records.total)]
    },
  )
}

fn watch6() -> tazuna.Machine(R6, E6) {
  tazuna.machine(
    name: "watch6",
    instances: fn(r: R6) { table.keys(r.items) },
    initial: Idle,
    on: fn(c: tazuna.MachineCtx(Int, Phase, R6), e: E6) {
      case c.state, e {
        Idle, Put6(k, _) if k == c.key -> tazuna.Enter(Waiting)
        _, _ -> tazuna.Stay
      }
    },
    timer: fn(c: tazuna.TimerCtx(Int, Phase, R6)) {
      case c.state, table.get(c.records.items, c.key) {
        Waiting, Some(at) -> Some(tazuna.Timer(at: at, enter: Pinging))
        _, _ -> None
      }
    },
    effect: fn(c: tazuna.MachineCtx(Int, Phase, R6)) {
      case c.state {
        Pinging ->
          Some(
            tazuna.request_command(
              command: send(),
              input: c.key,
              on_answer: fn(a) {
                case a {
                  Ok(Nil) -> [Ping6]
                  Error(_) -> []
                }
              },
            ),
          )
        _ -> None
      }
    },
    invariants: fn(c: tazuna.MachineCtx(Int, Phase, R6)) {
      [#("key is small", c.key < 10)]
    },
  )
}

fn again6() -> tazuna.Reaction(R6, E6) {
  tazuna.reaction(name: "again6", react: fn(_c: tazuna.ReactionCtx(R6), e: E6) {
    case e {
      Put6(k, _) -> [
        tazuna.send_command(command: bump6(), input: k, on_answer: fn(_a) { [] }),
      ]
      _ -> []
    }
  })
}

fn s6() -> tazuna.Service {
  tazuna.service(
    name: "s6",
    init: R6(items: table.new(), total: 0),
    apply: apply6,
    subscribes: [
      tazuna.subscribe(to: tick(), wrap: fn(t: Int) { Bumped6(t) }),
    ],
    declares: [
      tazuna.declare_command(put6()),
      tazuna.declare_command(del6()),
      tazuna.declare_command(bump6()),
    ],
    machines: [watch6()],
    reactions: [again6()],
    invariants: fn(r: R6) {
      [
        #("total not negative", r.total >= 0),
        #("few items", table.size(r.items) <= 2),
      ]
    },
    responses: [
      tazuna.response(
        name: "a put is pinged",
        after: fn(e: E6) {
          case e {
            Put6(_, _) -> True
            _ -> False
          }
        },
        then: fn(_trigger: E6, e: E6) {
          case e {
            Ping6 -> True
            _ -> False
          }
        },
        within: 20,
        deadline: fn(r: R6, trigger: E6) {
          case trigger {
            Put6(k, _) -> table.get(r.items, k)
            _ -> None
          }
        },
      ),
      tazuna.response(
        name: "a positive put is bumped",
        after: fn(e: E6) {
          case e {
            Put6(k, _) -> k > 0
            _ -> False
          }
        },
        then: fn(_trigger: E6, e: E6) {
          case e {
            Bumped6(_) -> True
            _ -> False
          }
        },
        within: 0,
        deadline: fn(_r: R6, _trigger: E6) { None },
      ),
    ],
    cascade: 2,
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [s1(), s2(), s3(), s4(), s5(), s6()], externals: [
    tazuna.external(name: "mail", declares: [
      tazuna.declare_external_command(send()),
      tazuna.declare_source(tick()),
    ]),
  ])
}

pub fn model() -> tazuna.Model {
  tazuna.model(spec: spec(), resource_limit: 50_000_000, scopes: [
    tazuna.scope(
      service: s1(),
      creates: [tazuna.create(table: fn(r: R1) { r.items }, at_most: 2)],
      others_at_most: 2,
      steps: 5,
      explore_depth: 0,
      explore_states: 1,
      waits: [],
      values: [],
    ),
    tazuna.scope(
      service: s2(),
      creates: [tazuna.create(table: fn(r: R2) { r.items }, at_most: 2)],
      others_at_most: 2,
      steps: 5,
      explore_depth: 0,
      explore_states: 1,
      waits: [],
      values: [],
    ),
    tazuna.scope(
      service: s3(),
      creates: [tazuna.create(table: fn(r: R3) { r.items }, at_most: 2)],
      others_at_most: 2,
      steps: 5,
      explore_depth: 0,
      explore_states: 1,
      waits: [],
      values: [],
    ),
    tazuna.scope(
      service: s4(),
      creates: [tazuna.create(table: fn(r: R4) { r.items }, at_most: 2)],
      others_at_most: 2,
      steps: 5,
      explore_depth: 0,
      explore_states: 1,
      waits: [],
      values: [],
    ),
    tazuna.scope(
      service: s5(),
      creates: [tazuna.create(table: fn(r: R5) { r.items }, at_most: 2)],
      others_at_most: 2,
      steps: 5,
      explore_depth: 0,
      explore_states: 1,
      waits: [],
      values: [],
    ),
    tazuna.scope(
      service: s6(),
      creates: [tazuna.create(table: fn(r: R6) { r.items }, at_most: 2)],
      others_at_most: 2,
      steps: 5,
      explore_depth: 0,
      explore_states: 1,
      waits: [],
      values: [],
    ),
  ])
}
