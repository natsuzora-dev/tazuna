//// A todo service: users add tasks and complete them, and an hour after a
//// task is added, if it is still open, the service mails a reminder.

import gleam/option.{None, Some}
import tazuna.{type Ctx, type Id, type MachineCtx, type QueryCtx}
import tazuna/table.{type Table}

/// The open tasks' titles. Completing a task removes it.
pub type Records {
  Records(tasks: Table(Id, String))
}

pub type Event {
  Added(task: Id, title: String)
  Completed(task: Id)
  ReminderDue(task: Id, title: String)
}

/// Who sends a request from outside.
pub type Caller {
  User
}

pub type Rejection {
  NoSuchTask
}

/// What the mailer is asked to send.
pub type Mail {
  Mail(subject: String)
}

pub type Bounced {
  Bounced
}

/// The reminder's lifecycle for one open task.
pub type Phase {
  Waiting
  Due
}

const hour: Int = 3_600_000

fn apply(ctx: tazuna.ApplyCtx(Records), event: Event) -> Records {
  let records = ctx.records
  case event {
    Added(id, title) -> Records(tasks: table.insert(records.tasks, id, title))
    Completed(id) -> Records(tasks: table.remove(records.tasks, id))
    ReminderDue(..) -> records
  }
}

fn add() -> tazuna.Command(Records, Event, Caller, String, tazuna.Never) {
  tazuna.command(
    name: "add",
    callers: [tazuna.Outside(User)],
    accepts: fn(title) { [#("title is not empty", title != "")] },
    decide: fn(ctx: Ctx(Records, String, Caller)) {
      Ok([Added(tazuna.fresh(ctx.fresh, 0), ctx.input)])
    },
    ensures: fn(ctx: Ctx(Records, String, Caller), after: Records) {
      [
        #(
          "the new task is open",
          table.get(after.tasks, tazuna.fresh(ctx.fresh, 0)) == Some(ctx.input),
        ),
      ]
    },
  )
}

fn complete() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "complete",
    callers: [tazuna.Outside(User)],
    accepts: fn(_id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use _title <- table.lookup(ctx.records.tasks, ctx.input, or: NoSuchTask)
      Ok([Completed(ctx.input)])
    },
    ensures: fn(ctx: Ctx(Records, Id, Caller), after: Records) {
      [
        #("the task is gone", table.get(after.tasks, ctx.input) == None),
      ]
    },
  )
}

fn remind() -> tazuna.Command(Records, Event, Caller, Id, Rejection) {
  tazuna.command(
    name: "remind",
    callers: [tazuna.Own],
    accepts: fn(_id) { [] },
    decide: fn(ctx: Ctx(Records, Id, Caller)) {
      use title <- table.lookup(ctx.records.tasks, ctx.input, or: NoSuchTask)
      Ok([ReminderDue(ctx.input, title)])
    },
    ensures: fn(_ctx, _after) { [] },
  )
}

fn open_tasks() -> tazuna.Query(Records, Caller, Nil, Int) {
  tazuna.query(
    name: "open tasks",
    callers: [tazuna.Outside(User)],
    accepts: fn(_input) { [] },
    resolve: fn(ctx: QueryCtx(Records, Nil, Caller)) {
      table.size(ctx.records.tasks)
    },
  )
}

fn send() -> tazuna.ExternalCommand(Mail, Nil, Bounced) {
  tazuna.external_command(name: "send")
}

/// One instance per open task. An hour after the task appears, the reminder
/// runs `remind`, so the log shows the reminder as a `ReminderDue` event.
fn reminder() -> tazuna.Machine(Records, Event) {
  tazuna.machine(
    name: "reminder",
    instances: fn(records: Records) { table.keys(records.tasks) },
    initial: Waiting,
    on: fn(_ctx, _event) { tazuna.Stay },
    after: fn(ctx: MachineCtx(Id, Phase, Records)) {
      case ctx.state {
        Waiting -> Some(tazuna.Timer(after: hour, enter: Due))
        Due -> None
      }
    },
    effect: fn(ctx: MachineCtx(Id, Phase, Records)) {
      case ctx.state {
        Waiting -> None
        Due ->
          Some(
            tazuna.send_command(
              command: remind(),
              input: ctx.key,
              on_answer: fn(_answer) { [] },
            ),
          )
      }
    },
    invariants: fn(_ctx) { [] },
  )
}

/// Each due reminder goes to the mailer.
fn mail() -> tazuna.Reaction(Records, Event) {
  tazuna.reaction(name: "mail", react: fn(_ctx, event) {
    case event {
      ReminderDue(_id, title) -> [
        tazuna.request_command(
          command: send(),
          input: Mail(subject: title),
          on_answer: fn(_answer) { [] },
        ),
      ]
      _ -> []
    }
  })
}

fn todo_service() -> tazuna.Service {
  tazuna.service(
    name: "todo",
    init: Records(tasks: table.new()),
    apply: apply,
    subscribes: [],
    declares: [
      tazuna.declare_command(add()),
      tazuna.declare_command(complete()),
      tazuna.declare_command(remind()),
      tazuna.declare_query(open_tasks()),
    ],
    machines: [reminder()],
    reactions: [mail()],
    invariants: fn(records: Records) {
      [
        #(
          "every title is not empty",
          table.all(records.tasks, satisfying: fn(_id, title) { title != "" }),
        ),
      ]
    },
    responses: [
      tazuna.response(
        name: "an added task is reminded or done within an hour",
        after: fn(event) {
          case event {
            Added(..) -> True
            _ -> False
          }
        },
        then: fn(trigger, event) {
          case trigger, event {
            Added(task:, ..), ReminderDue(task: reminded, ..) ->
              reminded == task
            Added(task:, ..), Completed(task: done) -> done == task
            _, _ -> False
          }
        },
        within: hour,
      ),
    ],
    bounds: tazuna.bounds(
      creates: [
        tazuna.create(table: fn(records: Records) { records.tasks }, at_most: 2),
      ],
      items: 1,
      cascade: 2,
      steps: 3,
    ),
    scenarios: [remind_the_open_task()],
  )
}

/// An add with an empty title is Invalid on purpose, to show the rule's name
/// in the answer. Then two tasks are added and one is completed; an hour later
/// only the open one is reminded.
fn remind_the_open_task() -> tazuna.Scenario(Records, Event, Caller) {
  tazuna.scenario(name: "remind the open task", steps: [
    tazuna.step_command(command: add(), caller: User, input: ""),
    {
      use milk <- tazuna.step_command_then(
        command: add(),
        caller: User,
        input: "Buy milk",
      )
      [
        tazuna.step_command(
          command: add(),
          caller: User,
          input: "Call the bank",
        ),
        tazuna.step_command(
          command: complete(),
          caller: User,
          input: tazuna.fresh(milk, 0),
        ),
        tazuna.step_query(query: open_tasks(), caller: User, input: Nil),
        tazuna.step_wait(for: hour),
        tazuna.step_answer_command(
          command: send(),
          sender: tazuna.from_reaction(reaction: mail()),
          with: Ok(Nil),
        ),
      ]
    },
  ])
}

pub fn spec() -> tazuna.Spec {
  tazuna.spec(services: [todo_service()], externals: [
    tazuna.external(name: "mailer", declares: [
      tazuna.declare_external_command(send()),
    ]),
  ])
}
