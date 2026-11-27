import gleam/option.{None}
import tazuna
import tazuna/bag

pub type Records {
  Records(open: List(Int))
}

pub type Event {
  Opened(at: List(Int))
}

pub type Phase {
  Idle
}

fn apply(_ctx: tazuna.ApplyCtx(Records), e: Event) -> Records {
  case e {
    Opened(at) -> Records(open: at)
  }
}

fn remind() -> tazuna.Machine(Records, Event) {
  tazuna.machine(
    name: "remind",
    instances: fn(r: Records) { bag.from_list(r.open) },
    initial: Idle,
    on: fn(_c: tazuna.MachineCtx(Int, Phase, Records), _e: Event) {
      tazuna.Stay
    },
    after: fn(_c: tazuna.MachineCtx(Int, Phase, Records)) { None },
    effect: fn(_c: tazuna.MachineCtx(Int, Phase, Records)) { None },
    invariants: fn(_c: tazuna.MachineCtx(Int, Phase, Records)) { [] },
  )
}

fn cells(name: String) -> tazuna.Service {
  tazuna.service(
    name: name,
    init: Records(open: [1]),
    apply: apply,
    subscribes: [],
    declares: [],
    machines: [remind()],
    reactions: [],
    invariants: fn(_r) { [] },
    responses: [],
    bounds: tazuna.bounds(creates: [], items: 3, cascade: 10, steps: 5),
    scenarios: [],
  )
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [cells("tasks")], externals: [])
}
