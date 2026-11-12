import { at, call, mock, restart, scenario, send, subscribe, unchecked, unsubscribe } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { device } from "../device/contract.ts";
import { reminderNotification } from "./automations.ts";
import { addTask, changeDue, changeReminders, completeTask, deleteTask, renameTask, reopenTask } from "./commands.ts";
import { businessDayReminder } from "./machines.ts";
import { reminderSettings, taskDetail, tasks } from "./queries.ts";

const addMilkUnanswered = [
  at("2026-10-25T10:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
] as const;
const addMilk = [
  ...addMilkUnanswered,
  mock(businessDayReminder, [calendar.nextBusinessDay, { result: "fulfilled", output: { day: "2026-10-26" } }]),
] as const;

export const completeTwice = scenario(
  "Complete a task twice; todo rejects the second completeTask by requires notCompleted",
  [
    ...addMilk,
    at("2026-10-25T10:01:00+09:00"),
    send(completeTask, { taskId: "task-1" }),
    send(completeTask, { taskId: "task-1" }),
  ],
);

export const remindAtDue = scenario("Change the due date of a task; todo sets the reminder time to the due date", [
  at("2026-10-25T10:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  mock(businessDayReminder, [calendar.nextBusinessDay, { result: "rejected", rejection: { kind: "unavailable" } }]),
  send(changeDue, { taskId: "task-1", dueAt: "2026-10-26T18:00:00+09:00" }),
  call(taskDetail, { taskId: "task-1" }),
]);

export const clearsDue = scenario(
  "Set and then clear the due date of a task; todo sets the reminder time to the start of the next business day, as for a task added without a due date",
  [
    ...addMilk,
    send(changeDue, { taskId: "task-1", dueAt: "2026-10-27T18:00:00+09:00" }),
    send(changeDue, { taskId: "task-1", dueAt: null }),
    mock(businessDayReminder, [calendar.nextBusinessDay, { result: "fulfilled", output: { day: "2026-10-26" } }]),
    call(tasks, { filter: "open" }),
  ],
);

export const filtersTasks = scenario(
  "Add two tasks, complete one, and call tasks with each filter; tasks returns the open, the completed, or all tasks",
  [
    ...addMilk,
    send(addTask, { taskId: "task-2", title: "Buy eggs" }),
    mock(businessDayReminder, [calendar.nextBusinessDay, { result: "fulfilled", output: { day: "2026-10-26" } }]),
    send(completeTask, { taskId: "task-1" }),
    call(tasks, { filter: "open" }),
    call(tasks, { filter: "completed" }),
    call(tasks, { filter: "all" }),
  ],
);

export const reopenCompleted = scenario("Complete a task and reopen it; tasks with filter open returns the task", [
  ...addMilk,
  at("2026-10-25T10:01:00+09:00"),
  send(completeTask, { taskId: "task-1" }),
  send(reopenTask, { taskId: "task-1" }),
  call(tasks, { filter: "open" }),
]);

export const rejectsReopenOpen = scenario("Reopen an open task; todo rejects reopenTask by requires completed", [
  ...addMilk,
  send(reopenTask, { taskId: "task-1" }),
]);

export const skipsPassedReminderOnReopen = scenario(
  "Complete a task and reopen it after its reminder time passes; todo does not remind the user of the task",
  [
    ...addMilk,
    send(completeTask, { taskId: "task-1" }),
    at("2026-10-26T09:00:00+09:00"),
    send(reopenTask, { taskId: "task-1" }),
    call(taskDetail, { taskId: "task-1" }),
  ],
);

export const remindsReopenedAtReminder = scenario(
  "Complete a task and reopen it before its reminder time; todo reminds the user of the task at the reminder time",
  [
    ...addMilk,
    send(completeTask, { taskId: "task-1" }),
    send(reopenTask, { taskId: "task-1" }),
    at("2026-10-26T00:00:00+09:00"),
  ],
);

export const deletesTask = scenario("Delete a task; tasks no longer returns the task, and taskDetail returns null", [
  ...addMilk,
  send(deleteTask, { taskId: "task-1" }),
  call(tasks, { filter: "all" }),
  call(taskDetail, { taskId: "task-1" }),
]);

export const rejectsPastDue = scenario(
  "Change the due date of a task to a past time; todo rejects changeDue by requires notPast",
  [...addMilk, send(changeDue, { taskId: "task-1", dueAt: "2026-10-25T09:00:00+09:00" })],
);

export const remindAtRemindAt = scenario("Let the reminder time of a task arrive; todo reminds the user of the task", [
  ...addMilk,
  at("2026-10-25T23:59:59+09:00"),
  at("2026-10-26T00:00:00+09:00"),
]);

export const remindsAfterNotShown = scenario(
  "Let device fail to show a reminder, and let the reminder time of the next task arrive; todo reminds the user of that task",
  [
    ...addMilk,
    send(addTask, { taskId: "task-2", title: "Buy eggs" }),
    mock(businessDayReminder, [calendar.nextBusinessDay, { result: "fulfilled", output: { day: "2026-10-27" } }]),
    at("2026-10-26T00:00:00+09:00"),
    mock(reminderNotification, [device.showNotification, { result: "rejected", rejection: { kind: "unavailable" } }]),
    at("2026-10-27T00:00:00+09:00"),
    mock(reminderNotification, [device.showNotification, { result: "accepted" }]),
  ],
);

export const answersSubscriptions = scenario(
  "Subscribe to tasks and taskDetail, and complete a task; todo sends a new answer for each subscription whose answer changes",
  [
    ...addMilk,
    subscribe(tasks, { filter: "open" }, { id: "s1" }),
    subscribe(taskDetail, { taskId: "task-1" }, { id: "s2" }),
    send(completeTask, { taskId: "task-1" }),
    unsubscribe("s1"),
    unsubscribe("s2"),
  ],
);

export const completeRedelivered = scenario(
  "Send completeTask twice with the same command id; todo does not process the second and returns the first answer",
  [
    ...addMilk,
    send(completeTask, { taskId: "task-1" }, { id: "c9" }),
    send(completeTask, { taskId: "task-1" }, { id: "c9" }),
  ],
);

export const remindAddedWhileAsking = scenario(
  "Add a task while todo asks calendar for the next business day; todo also asks for the added task without waiting for the answer",
  [
    ...addMilkUnanswered,
    send(addTask, { taskId: "task-2", title: "Buy eggs" }),
    mock(businessDayReminder, [calendar.nextBusinessDay, { result: "fulfilled", output: { day: "2026-10-26" } }]),
    mock(businessDayReminder, [calendar.nextBusinessDay, { result: "fulfilled", output: { day: "2026-10-26" } }]),
  ],
);

export const remindInAnswerOrder = scenario(
  "Add two tasks, and let the answer for the second arrive first; todo sets the reminder time of the second task first",
  [
    ...addMilkUnanswered,
    at("2026-10-26T10:05:00+09:00"),
    send(addTask, { taskId: "task-2", title: "Buy eggs" }),
    mock(businessDayReminder, [
      calendar.nextBusinessDay,
      { result: "fulfilled", output: { day: "2026-10-27" } },
      { input: { from: "2026-10-26" } },
    ]),
    mock(businessDayReminder, [calendar.nextBusinessDay, { result: "rejected", rejection: { kind: "unavailable" } }]),
  ],
);

export const skipsBusinessDayReminderWhenDisabled = scenario(
  "Turn reminders off, and let the reminder time set to the start of the next business day arrive; todo does not remind the user",
  [
    ...addMilk,
    send(changeReminders, { shouldRemind: false }),
    call(reminderSettings, {}),
    at("2026-10-26T00:00:00+09:00"),
  ],
);

export const skipsDueReminderWhenDisabled = scenario(
  "Turn reminders off, change the due date of a task, and let the due date arrive; todo sets the reminder time to the due date but does not remind the user",
  [
    ...addMilk,
    send(changeReminders, { shouldRemind: false }),
    send(changeDue, { taskId: "task-1", dueAt: "2026-10-27T18:00:00+09:00" }),
    at("2026-10-27T18:00:00+09:00"),
  ],
);

export const remindsWhenReenabled = scenario(
  "Turn reminders off and back on before the reminder time; todo reminds the user at the reminder time",
  [
    ...addMilk,
    send(changeReminders, { shouldRemind: false }),
    send(changeReminders, { shouldRemind: true }),
    at("2026-10-26T00:00:00+09:00"),
  ],
);

export const rejectsMalformedTitle = scenario(
  "Add a task whose title is not a string; todo rejects addTask as invalid-input",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "task-1", title: unchecked(7) })],
);

export const rejectsMissingTask = scenario(
  "Complete and reopen a task that does not exist; todo rejects completeTask and reopenTask as not-found",
  [at("2026-10-25T10:00:00+09:00"), send(completeTask, { taskId: "task-9" }), send(reopenTask, { taskId: "task-9" })],
);

export const renamesTask = scenario("Rename a task; taskDetail returns the new title", [
  ...addMilk,
  send(renameTask, { taskId: "task-1", title: "Buy soy milk" }),
  call(taskDetail, { taskId: "task-1" }),
]);

export const asksBusinessDayAgainOnStart = scenario(
  "Restart the server while todo asks calendar for the next business day; todo asks again for each task whose reminder time is pending",
  [
    ...addMilkUnanswered,
    at("2026-10-25T10:05:00+09:00"),
    restart(),
    mock(businessDayReminder, [calendar.nextBusinessDay, { result: "fulfilled", output: { day: "2026-10-26" } }]),
    call(taskDetail, { taskId: "task-1" }),
  ],
);
