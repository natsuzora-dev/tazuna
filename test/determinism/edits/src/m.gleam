import gleam/option.{type Option, None, Some}
import tazuna.{type Ctx}

pub type Records {
  Records(total: Int, last: Option(Int))
}

pub type Event {
  Added(amount: Int)
  Audited(amount: Int)
}

pub type Caller {
  User
}

fn send() -> tazuna.ExternalCommand(Int, Nil, Nil) {
  tazuna.external_command(name: "send")
}

fn apply(ctx: tazuna.ApplyCtx(Records), e: Event) -> Records {
  let r = ctx.records
  case e {
    Added(got) -> Records(..r, total: r.total + got)
    Audited(got) -> Records(..r, last: Some(got))
  }
}

fn add() -> tazuna.Command(Records, Event, Caller, Int, tazuna.Never) {
  tazuna.command(
    name: "add",
    callers: [tazuna.Outside(User)],
    accepts: fn(got: Int) { [#("positive", got > 0)] },
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
    accepts: fn(_got: Int) { [] },
    decide: fn(c: Ctx(Records, Int, Caller)) { Ok([Audited(c.input)]) },
    ensures: fn(_c, _r) { [] },
  )
}

/// A generic helper written once and used at two types: each use is its own place.
fn audit_noting(got: Int, _note: a) -> tazuna.Effect(Event) {
  tazuna.send_command(command: audit(), input: got, on_answer: fn(_a) { [] })
}

fn notify() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(
    name: "notify",
    react: fn(_c: tazuna.ReactionCtx(Records), e: Event) {
      case e {
        Added(got) -> [
          tazuna.request_command(command: send(), input: got, on_answer: fn(_a) {
            [Audited(got)]
          }),
          tazuna.send_command(command: audit(), input: got, on_answer: fn(_a) {
            []
          }),
          audit_noting(got, Nil),
        ]
        Audited(_) -> []
      }
    },
  )
}

fn recheck() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(
    name: "recheck",
    react: fn(_c: tazuna.ReactionCtx(Records), e: Event) {
      case e {
        Added(got) -> [
          tazuna.send_command(command: audit(), input: got, on_answer: fn(_a) {
            [Audited(got)]
          }),
          tazuna.send_command(
            command: audit(),
            input: got + 1,
            on_answer: fn(_a) { [] },
          ),
          audit_noting(got, 0),
        ]
        Audited(_) -> []
      }
    },
  )
}

fn counter() -> tazuna.Service {
  tazuna.service(
    name: "counter",
    init: Records(total: 0, last: None),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(add()), tazuna.declare_command(audit())],
    machines: [],
    reactions: [notify(), recheck()],
    invariants: fn(r: Records) { [#("not negative", r.total >= 0)] },
    responses: [],
    cascade: 4,
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

pub fn model() -> tazuna.Model {
  tazuna.model(spec: spec(), resource_limit: 50_000_000, scopes: [
    tazuna.scope(
      service: counter(),
      creates: [],
      others_at_most: 1,
      steps: 3,
      explore_depth: 2,
      explore_states: 50,
      waits: [],
      values: [],
    ),
  ])
}
