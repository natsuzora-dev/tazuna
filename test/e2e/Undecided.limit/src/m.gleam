import tazuna.{type Ctx}
import tazuna/table.{type Table}

pub type Records {
  Records(seen: Table(Int, Int), last: Table(Int, Int))
}

pub type Event {
  Seen(value: Int)
}

pub type Caller {
  User
}

fn apply(r: Records, e: Event) -> Records {
  case e {
    Seen(n) ->
      Records(seen: table.insert(r.seen, n, n), last: table.insert(r.last, n, n))
  }
}

fn see() -> tazuna.Command(Records, Event, Caller, Int, Nil) {
  tazuna.command(
    name: "see",
    callers: [User],
    accepts: fn(_n: Int) { [] },
    decide: fn(c: Ctx(Records, Int, Caller)) { Ok([Seen(c.input)]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn watcher() -> tazuna.Service {
  tazuna.service(
    name: "watcher",
    init: Records(seen: table.new(), last: table.new()),
    apply: apply,
    subscribes: [],
    declares: [tazuna.declare_command(see())],
    machines: [],
    reactions: [],
    invariants: fn(r: Records) { [#("in step", [r.seen] == [r.last])] },
    responses: [],
    bounds: tazuna.bounds(
      creates: [
        tazuna.create(table: fn(r: Records) { r.seen }, at_most: 2),
        tazuna.create(table: fn(r: Records) { r.last }, at_most: 2),
      ],
      items: 1,
      cascade: 1,
      steps: 5,
    ),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [watcher()], externals: [])
}
