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

fn send() -> tazuna.ExternalCommand(Int, Nil, Nil) {
  tazuna.external_command(name: "send")
}

fn apply(r: Records, e: Event) -> Records {
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

fn audit() -> tazuna.Command(Records, Event, Caller, Int, tazuna.Never) {
  tazuna.command(
    name: "audit",
    callers: [tazuna.Own],
    accepts: fn(_n: Int) { [] },
    decide: fn(_c: Ctx(Records, Int, Caller)) { Ok([]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn notify() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(
    name: "notify",
    react: fn(_c: tazuna.ReactionCtx(Records), e: Event) {
      case e {
        Added(n) -> [
          tazuna.request_command(command: send(), input: n, on_answer: fn(_a) {
            []
          }),
          tazuna.send_command(command: audit(), input: n, on_answer: fn(_a) {
            []
          }),
        ]
      }
    },
  )
}

fn counter() -> tazuna.Service {
  tazuna.service(
    name: "counter",
    init: Records(total: 0),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(add()), tazuna.declare_command(audit())],
    machines: [],
    reactions: [notify()],
    invariants: fn(r: Records) { [#("not negative", r.total >= 0)] },
    responses: [],
    bounds: tazuna.bounds(creates: [], items: 1, cascade: 1, steps: 5),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [counter()], externals: [
    tazuna.external(name: "mail", declares: [
      tazuna.declare_external_command(send()),
    ]),
  ])
}
