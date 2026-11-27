import tazuna.{type Ctx}

pub type Records {
  Records(count: Int)
}

pub type Event {
  Bumped
}

pub type Caller {
  User
}

fn apply(ctx: tazuna.ApplyCtx(Records), _e: Event) -> Records {
  let r = ctx.records
  Records(count: r.count + 1)
}

fn nobody() -> tazuna.Command(Records, Event, Caller, Nil, tazuna.Never) {
  tazuna.command(
    name: "nobody",
    callers: [],
    accepts: fn(_n: Nil) { [] },
    decide: fn(_c: Ctx(Records, Nil, Caller)) { Ok([Bumped]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn unsent() -> tazuna.Command(Records, Event, Caller, Nil, tazuna.Never) {
  tazuna.command(
    name: "unsent",
    callers: [tazuna.Outside(User), tazuna.Own],
    accepts: fn(_n: Nil) { [] },
    decide: fn(_c: Ctx(Records, Nil, Caller)) { Ok([Bumped]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn outside() -> tazuna.Command(Records, Event, Caller, Nil, tazuna.Never) {
  tazuna.command(
    name: "outside",
    callers: [tazuna.Outside(User)],
    accepts: fn(_n: Nil) { [] },
    decide: fn(_c: Ctx(Records, Nil, Caller)) { Ok([Bumped]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn again() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(name: "again", react: fn(_c, _e: Event) {
    [
      tazuna.send_command(command: outside(), input: Nil, on_answer: fn(_a) {
        []
      }),
    ]
  })
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(
    services: [
      tazuna.service(
        name: "counter",
        init: Records(count: 0),
        apply: apply,
        subscribes: [],
        declares: [
          tazuna.declare_command(nobody()),
          tazuna.declare_command(unsent()),
          tazuna.declare_command(outside()),
        ],
        machines: [],
        reactions: [again()],
        invariants: fn(_r) { [] },
        responses: [],
        bounds: tazuna.bounds(creates: [], others_at_most: 1, cascade: 2, steps: 2),
        scenarios: [],
      ),
    ],
    externals: [],
  )
}
