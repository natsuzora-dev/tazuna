import tazuna

pub type Records {
  Records(sent: Int)
}

pub type Event {
  Sent
}

fn apply(r: Records, _e: Event) -> Records {
  Records(sent: r.sent + 1)
}

fn ping() -> tazuna.ExternalCommand(Int, Nil, Nil) {
  tazuna.external_command(name: "ping")
}

fn again() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(
    name: "again",
    react: fn(_c: tazuna.ReactionCtx(Records), _e: Event) {
      [tazuna.request_command(command: ping(), input: 1, on_answer: fn(_a) { [] })]
    },
  )
}

fn mail(name: String) -> tazuna.Service {
  tazuna.service(
    name: name,
    init: Records(sent: 0),
    apply: apply,
    subscribes: [],
    declares: [],
    machines: [],
    reactions: [again()],
    invariants: fn(_r) { [] },
    responses: [],
    bounds: tazuna.bounds(creates: [], items: 3, cascade: 10, steps: 5),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [mail("mail")], externals: [])
}
