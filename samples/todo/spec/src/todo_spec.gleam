//// A todo service: users add tasks and complete them, and an hour after a
//// task is added, if it is still open, the service mails a reminder.

import gleam/option.{None, Some}
import tazuna.{type Ctx, type Id, type MachineCtx, type QueryCtx, type TimerCtx}
import tazuna/duration
import tazuna/instant.{type Instant}
import tazuna/table.{type Table}

/// An open task: its title, when it is due for a reminder, and whether the
/// reminder went out.
pub type Task {
  Task(title: String, remind_at: Instant, reminded: Bool)
}

/// The open tasks. Completing a task removes it.
pub type Records {
  Records(tasks: Table(Id, Task))
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

fn apply(ctx: tazuna.ApplyCtx(Records), event: Event) -> Records {
  let records = ctx.records
  case event {
    Added(id, title) ->
      Records(tasks: table.insert(
        records.tasks,
        id,
        Task(
          title: title,
          remind_at: instant.add(ctx.now, duration.hours(1)),
          reminded: False,
        ),
      ))
    Completed(id) -> Records(tasks: table.remove(records.tasks, id))
    ReminderDue(id, _title) ->
      case table.get(records.tasks, id) {
        Some(task) ->
          Records(tasks: table.insert(
            records.tasks,
            id,
            Task(..task, reminded: True),
          ))
        None -> records
      }
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
          table.get(after.tasks, tazuna.fresh(ctx.fresh, 0))
            == Some(Task(
            title: ctx.input,
            remind_at: instant.add(ctx.now, duration.hours(1)),
            reminded: False,
          )),
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
      use _task <- table.lookup(ctx.records.tasks, ctx.input, or: NoSuchTask)
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
      use task <- table.lookup(ctx.records.tasks, ctx.input, or: NoSuchTask)
      Ok([ReminderDue(ctx.input, task.title)])
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

/// One instance per open task. At the task's `remind_at`, the reminder runs
/// `remind`, so the log shows the reminder as a `ReminderDue` event.
fn reminder() -> tazuna.Machine(Records, Event) {
  tazuna.machine(
    name: "reminder",
    instances: fn(records: Records) { table.keys(records.tasks) },
    initial: Waiting,
    on: fn(_ctx, _event) { tazuna.Stay },
    timer: fn(ctx: TimerCtx(Id, Phase, Records)) {
      case ctx.state, table.get(ctx.records.tasks, ctx.key) {
        Waiting, Some(task) ->
          Some(tazuna.Timer(at: task.remind_at, enter: Due))
        _, _ -> None
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
    invariants: fn(ctx: MachineCtx(Id, Phase, Records)) {
      [
        #(
          "a due reminder went out",
          case ctx.state, table.get(ctx.records.tasks, ctx.key) {
            Due, Some(task) -> task.reminded
            _, _ -> True
          },
        ),
      ]
    },
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
          table.all(records.tasks, satisfying: fn(_id, task: Task) {
            task.title != ""
          }),
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
        within: duration.hours(1),
        deadline: fn(records: Records, trigger: Event) {
          case trigger {
            Added(task:, ..) ->
              case table.get(records.tasks, task) {
                Some(open) ->
                  case open.reminded {
                    True -> None
                    False -> Some(open.remind_at)
                  }
                None -> None
              }
            _ -> None
          }
        },
      ),
    ],
    cascade: 2,
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
        tazuna.step_wait(for: duration.hours(1)),
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

/// How far prove and generate look: at most two open tasks, one item in every
/// other collection, and runs of up to three inputs.
pub fn model() -> tazuna.Model {
  tazuna.model(spec: spec(), resource_limit: 50_000_000, scopes: [
    tazuna.scope(
      service: todo_service(),
      creates: [
        tazuna.create(table: fn(records: Records) { records.tasks }, at_most: 2),
      ],
      others_at_most: 1,
      steps: 3,
      explore_depth: 6,
      explore_states: 10_000,
      waits: [duration.hours(1)],
      values: [],
    ),
  ])
}
