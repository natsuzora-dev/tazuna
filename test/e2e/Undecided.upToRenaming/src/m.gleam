import gleam/option.{type Option, None, Some}
import tazuna.{type Ctx, type Id}

pub type Records {
  Records(last: Option(Id))
}

pub type Event {
  Went
  Marked(id: Id)
}

pub type Caller {
  User
}

fn apply(r: Records, e: Event) -> Records {
  case e {
    Went -> r
    Marked(id) -> Records(last: Some(id))
  }
}

fn go() -> tazuna.Command(Records, Event, Caller, Nil, tazuna.Never) {
  tazuna.command(
    name: "go",
    callers: [tazuna.Outside(User)],
    accepts: fn(_n: Nil) { [] },
    decide: fn(_c: Ctx(Records, Nil, Caller)) { Ok([Went]) },
    ensures: fn(_c: Ctx(Records, Nil, Caller), _r: Records) { [] },
  )
}

fn mark() -> tazuna.Command(Records, Event, Caller, Nil, tazuna.Never) {
  tazuna.command(
    name: "mark",
    callers: [tazuna.Outside(User), tazuna.Own],
    accepts: fn(_n: Nil) { [] },
    decide: fn(c: Ctx(Records, Nil, Caller)) {
      Ok([Marked(tazuna.fresh(c.fresh, 0))])
    },
    ensures: fn(_c: Ctx(Records, Nil, Caller), _r: Records) { [] },
  )
}

fn twice() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(
    name: "twice",
    react: fn(_c: tazuna.ReactionCtx(Records), e: Event) {
      case e {
        Went -> [send_mark(), send_mark()]
        Marked(_) -> []
      }
    },
  )
}

fn send_mark() -> tazuna.Effect(Event) {
  tazuna.send_command(command: mark(), input: Nil, on_answer: fn(_a) { [] })
}

fn marks() -> tazuna.Service {
  tazuna.service(
    name: "marks",
    init: Records(last: None),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(go()), tazuna.declare_command(mark())],
    machines: [],
    reactions: [twice()],
    invariants: fn(_r: Records) { [] },
    responses: [],
    bounds: tazuna.bounds(creates: [], items: 2, cascade: 2, steps: 3),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [marks()], externals: [])
}
