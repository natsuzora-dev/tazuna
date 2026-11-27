import tazuna.{type Ctx}

pub type Records {
  Records(sent: Int)
}

pub type Event {
  Sent
}

fn apply(ctx: tazuna.ApplyCtx(Records), _e: Event) -> Records {
  let r = ctx.records
  Records(sent: r.sent + 1)
}

pub type Caller {
  User
}

fn bump() -> tazuna.Command(Records, Event, Caller, Int, tazuna.Never) {
  tazuna.command(
    name: "bump",
    callers: [tazuna.Outside(User), tazuna.Own],
    accepts: fn(_n) { [] },
    decide: fn(_c: Ctx(Records, Int, Caller)) { Ok([Sent]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn ping() -> tazuna.ExternalCommand(Int, Nil, Nil) {
  tazuna.external_command(name: "ping")
}

fn again() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(
    name: "again",
    react: fn(_c: tazuna.ReactionCtx(Records), _e: Event) {
      [
        tazuna.request_command(command: ping(), input: 1, on_answer: fn(_a) {
          []
        }),
        tazuna.send_command(
          command: bump(),
          input: 1,
          on_answer: fn(_a) { [] },
        ),
      ]
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
