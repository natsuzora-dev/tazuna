import gleam/option.{type Option, None, Some}
import tazuna.{type Ctx, type Id}
import tazuna/duration

pub type Records {
  Records(total: Int)
}

pub type Event {
  Added(amount: Int)
}

pub type Caller {
  User
}

fn apply(ctx: tazuna.ApplyCtx(Records), e: Event) -> Records {
  let r = ctx.records
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

fn counter() -> tazuna.Service {
  tazuna.service(
    name: "counter",
    init: Records(total: 0),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(add())],
    machines: [],
    reactions: [],
    invariants: fn(r: Records) { [#("not negative", r.total >= 0)] },
    responses: [
      tazuna.response(
        name: "an add shows its own amount",
        after: fn(_e) { True },
        then: fn(trigger, e) { trigger == e },
        within: duration.milliseconds(0),
        deadline: fn(_r: Records, _trigger: Event) { None },
      ),
    ],
    cascade: 1,
    scenarios: [],
  )
}

/// Two `mark`s waiting together commute only with the counters they make swapped: `last` holds the second one's id.
pub type MarkRecords {
  MarkRecords(last: Option(Id))
}

pub type MarkEvent {
  Went
  Marked(id: Id)
}

fn apply_mark(ctx: tazuna.ApplyCtx(MarkRecords), e: MarkEvent) -> MarkRecords {
  case e {
    Went -> ctx.records
    Marked(id) -> MarkRecords(last: Some(id))
  }
}

fn go() -> tazuna.Command(MarkRecords, MarkEvent, Caller, Nil, tazuna.Never) {
  tazuna.command(
    name: "go",
    callers: [tazuna.Outside(User)],
    accepts: fn(_n: Nil) { [] },
    decide: fn(_c: Ctx(MarkRecords, Nil, Caller)) { Ok([Went]) },
    ensures: fn(_c: Ctx(MarkRecords, Nil, Caller), _r: MarkRecords) { [] },
  )
}

fn mark() -> tazuna.Command(MarkRecords, MarkEvent, Caller, Nil, tazuna.Never) {
  tazuna.command(
    name: "mark",
    callers: [tazuna.Outside(User), tazuna.Own],
    accepts: fn(_n: Nil) { [] },
    decide: fn(c: Ctx(MarkRecords, Nil, Caller)) {
      Ok([Marked(tazuna.fresh(c.fresh, 0))])
    },
    ensures: fn(_c: Ctx(MarkRecords, Nil, Caller), _r: MarkRecords) { [] },
  )
}

fn twice() -> tazuna.Reaction(MarkRecords, MarkEvent) {
  tazuna.reaction(
    name: "twice",
    react: fn(_c: tazuna.ReactionCtx(MarkRecords), e: MarkEvent) {
      case e {
        Went -> [send_mark(), send_mark()]
        Marked(_) -> []
      }
    },
  )
}

fn send_mark() -> tazuna.Effect(MarkEvent) {
  tazuna.send_command(command: mark(), input: Nil, on_answer: fn(_a) { [] })
}

fn marks() -> tazuna.Service {
  tazuna.service(
    name: "marks",
    init: MarkRecords(last: None),
    apply: apply_mark,
    subscribes: [],
    declares: [tazuna.declare_command(go()), tazuna.declare_command(mark())],
    machines: [],
    reactions: [twice()],
    invariants: fn(_r: MarkRecords) { [] },
    responses: [],
    cascade: 2,
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [counter(), marks()], externals: [])
}

pub fn model() -> tazuna.Model {
  tazuna.model(spec: spec(), resource_limit: 50_000_000, scopes: [
    tazuna.scope(
      service: counter(),
      creates: [],
      others_at_most: 1,
      steps: 5,
      explore_depth: 0,
      explore_states: 1,
      waits: [],
      values: [],
    ),
    tazuna.scope(
      service: marks(),
      creates: [],
      others_at_most: 2,
      steps: 3,
      explore_depth: 0,
      explore_states: 1,
      waits: [],
      values: [],
    ),
  ])
}
