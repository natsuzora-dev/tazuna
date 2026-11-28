import tazuna.{type Ctx}
import tazuna/bag.{type Bag}

pub type Records {
  Records(tags: Bag(String))
}

pub type Event {
  Tagged(name: String)
  Crowded
}

pub type Caller {
  User
}

fn apply(ctx: tazuna.ApplyCtx(Records), e: Event) -> Records {
  let r = ctx.records
  case e {
    Tagged(t) -> Records(tags: bag.insert(r.tags, t))
    Crowded -> r
  }
}

fn tag() -> tazuna.Command(Records, Event, Caller, String, tazuna.Never) {
  tazuna.command(
    name: "tag",
    callers: [tazuna.Outside(User)],
    accepts: fn(_t) { [] },
    decide: fn(c: Ctx(Records, String, Caller)) {
      case bag.size(c.records.tags) >= 2 {
        True -> Ok([Crowded])
        False -> Ok([Tagged(c.input)])
      }
    },
    ensures: fn(_c, _r) { [] },
  )
}

fn tags() -> tazuna.Service {
  tazuna.service(
    name: "tags",
    init: Records(tags: bag.from_list([])),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(tag())],
    machines: [],
    reactions: [],
    invariants: fn(_r) { [] },
    responses: [],
    cascade: 1,
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [tags()], externals: [])
}

pub fn model() -> tazuna.Model {
  tazuna.model(spec: spec(), resource_limit: 50_000_000, scopes: [
    tazuna.scope(
      service: tags(),
      creates: [],
      others_at_most: 1,
      steps: 3,
      explore_depth: 0,
      explore_states: 1,
      waits: [],
      values: [],
    ),
  ])
}
