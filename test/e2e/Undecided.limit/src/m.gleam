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

fn apply(ctx: tazuna.ApplyCtx(Records), e: Event) -> Records {
  let r = ctx.records
  case e {
    Seen(n) ->
      Records(
        seen: table.insert(r.seen, n, n),
        last: table.insert(r.last, n, n),
      )
  }
}

fn see() -> tazuna.Command(Records, Event, Caller, Int, tazuna.Never) {
  tazuna.command(
    name: "see",
    callers: [tazuna.Outside(User)],
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

// The two orders of asker's own commands end with the same data but keep different on_answer functions, whose
// results prove does not compare.
pub type AskRecords {
  AskRecords(flag: Bool)
}

pub type AskEvent {
  Went
  Set
  Asked
}

fn ask_apply(ctx: tazuna.ApplyCtx(AskRecords), e: AskEvent) -> AskRecords {
  let r = ctx.records
  case e {
    Set -> AskRecords(flag: True)
    _ -> r
  }
}

fn go() -> tazuna.Command(AskRecords, AskEvent, Caller, Nil, tazuna.Never) {
  tazuna.command(
    name: "go",
    callers: [tazuna.Outside(User)],
    accepts: fn(_n: Nil) { [] },
    decide: fn(_c: Ctx(AskRecords, Nil, Caller)) { Ok([Went]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn set() -> tazuna.Command(AskRecords, AskEvent, Caller, Nil, tazuna.Never) {
  tazuna.command(
    name: "set",
    callers: [tazuna.Outside(User), tazuna.Own],
    accepts: fn(_n: Nil) { [] },
    decide: fn(_c: Ctx(AskRecords, Nil, Caller)) { Ok([Set]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn ask() -> tazuna.Command(AskRecords, AskEvent, Caller, Nil, tazuna.Never) {
  tazuna.command(
    name: "ask",
    callers: [tazuna.Outside(User), tazuna.Own],
    accepts: fn(_n: Nil) { [] },
    decide: fn(_c: Ctx(AskRecords, Nil, Caller)) { Ok([Asked]) },
    ensures: fn(_c, _r) { [] },
  )
}

fn ping() -> tazuna.ExternalCommand(Int, Nil, Nil) {
  tazuna.external_command(name: "ping")
}

fn both() -> tazuna.Reaction(AskRecords, AskEvent) {
  tazuna.reaction(
    name: "both",
    react: fn(c: tazuna.ReactionCtx(AskRecords), e: AskEvent) {
      case e {
        Went -> [
          tazuna.send_command(
            command: set(),
            input: Nil,
            on_answer: fn(_a) { [] },
          ),
          tazuna.send_command(
            command: ask(),
            input: Nil,
            on_answer: fn(_a) { [] },
          ),
        ]
        Asked ->
          case c.records.flag {
            True -> [
              tazuna.request_command(
                command: ping(),
                input: 1,
                on_answer: fn(_a) { [] },
              ),
            ]
            False -> [
              tazuna.request_command(
                command: ping(),
                input: 1,
                on_answer: fn(_b) { [] },
              ),
            ]
          }
        Set -> []
      }
    },
  )
}

fn asker() -> tazuna.Service {
  tazuna.service(
    name: "asker",
    init: AskRecords(flag: False),
    apply: ask_apply,
    subscribes: [],
    declares: [
      tazuna.declare_command(go()),
      tazuna.declare_command(set()),
      tazuna.declare_command(ask()),
    ],
    machines: [],
    reactions: [both()],
    invariants: fn(_r: AskRecords) { [] },
    responses: [],
    bounds: tazuna.bounds(creates: [], items: 2, cascade: 3, steps: 3),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [watcher(), asker()], externals: [
    tazuna.external(name: "mail", declares: [
      tazuna.declare_external_command(ping()),
    ]),
  ])
}
