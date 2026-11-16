import {
  answered,
  emitted,
  event,
  external,
  request,
  requested,
  skip,
  unchecked,
  type When,
} from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { device } from "../device/contract.ts";
import { notifier } from "../notifier/contract.ts";
import { screens } from "../screens/contract.ts";
import { addTask, changeDue, changeReminders, completeTask, deleteTask, renameTask, reopenTask } from "./commands.ts";
import { scenario } from "./data.ts";
import { taskCompleted, taskDeleted, taskReopened } from "./events.ts";
import { reminderSettings, taskDetail, tasks } from "./queries.ts";

const peers = {
  calendar: external(calendar),
  device: external(device),
  notifier: skip(notifier, "notifier's reactions to todo's events are notifier's scenarios"),
  screens: skip(screens, "the screens' subscriptions are the screens' scenarios"),
} as const;
type W = When<typeof peers>;

const noTasks = {
  start: "2026-10-25T10:00:00+09:00",
  records: { Task: [], Settings: { shouldRemind: true } },
  peers,
} as const;

const accepted = { result: "accepted" } as const;
const unavailable = { result: "rejected", rejection: { kind: "unavailable" } } as const;
const requires = (reason: string) => ({ result: "rejected", rejection: { kind: "requires", reason } }) as const;
const day = (d: string) => ({ result: "fulfilled", output: { day: d } }) as const;
const fulfilled = <O>(output: O) => ({ result: "fulfilled", output }) as const;

const milkRow = { taskId: "task-1", title: "Buy milk", dueAt: null, completedAt: null } as const;
const milkDetail = {
  title: "Buy milk",
  isCompleted: false,
  dueAt: null,
  createdAt: "2026-10-25T10:00:00+09:00",
  remindAt: "2026-10-26T00:00:00+09:00",
} as const;
const showMilk = request(device.showNotification, { text: "Buy milk" });

/** client adds task-1; calendar has not answered yet. */
const addMilkUnanswered = (w: W) => w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });

/** client adds task-1, and calendar answers the business-day request that adding caused. */
const addMilk = (w: W) => {
  const add = addMilkUnanswered(w);
  w.peer.calendar.answer(add.request(calendar.nextBusinessDay), day("2026-10-26"));
  return add;
};

export const completeTwice = scenario(
  "Complete a task twice; todo rejects the second completeTask by requires notCompleted",
  {
    given: noTasks,
    when: (w) => {
      addMilk(w);
      w.clock.at("2026-10-25T10:01:00+09:00");
      const first = w.client.send(completeTask, { taskId: "task-1" });
      const second = w.client.send(completeTask, { taskId: "task-1" });
      return { first, second };
    },
    then: ({ first, second }) => [
      answered(first, accepted),
      emitted(first, [event(taskCompleted, { taskId: "task-1" })]),
      answered(second, requires("notCompleted")),
      emitted(second, []),
    ],
  },
);

export const remindAtDue = scenario("Change the due date of a task; todo sets the reminder time to the due date", {
  given: noTasks,
  when: (w) => {
    const add = addMilkUnanswered(w);
    w.peer.calendar.answer(add.request(calendar.nextBusinessDay), unavailable);
    w.client.send(changeDue, { taskId: "task-1", dueAt: "2026-10-26T18:00:00+09:00" });
    const detail = w.client.call(taskDetail, { taskId: "task-1" });
    return { detail };
  },
  then: ({ detail }) => [
    answered(
      detail,
      fulfilled({
        task: { ...milkDetail, dueAt: "2026-10-26T18:00:00+09:00", remindAt: "2026-10-26T18:00:00+09:00" },
      }),
    ),
  ],
});

export const clearsDue = scenario(
  "Set and then clear the due date of a task; todo sets the reminder time to the start of the next business day, as for a task added without a due date",
  {
    given: noTasks,
    when: (w) => {
      addMilk(w);
      w.client.send(changeDue, { taskId: "task-1", dueAt: "2026-10-27T18:00:00+09:00" });
      const clear = w.client.send(changeDue, { taskId: "task-1", dueAt: null });
      w.peer.calendar.answer(clear.request(calendar.nextBusinessDay), day("2026-10-26"));
      const open = w.client.call(tasks, { filter: "open" });
      return { clear, open };
    },
    then: ({ clear, open }) => [
      answered(clear, accepted),
      requested(clear, [request(calendar.nextBusinessDay, { from: "2026-10-25" })]),
      answered(open, fulfilled({ tasks: [milkRow] })),
    ],
  },
);

export const filtersTasks = scenario(
  "Add two tasks, complete one, and call tasks with each filter; tasks returns the open, the completed, or all tasks",
  {
    given: noTasks,
    when: (w) => {
      addMilk(w);
      const eggs = w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
      w.peer.calendar.answer(eggs.request(calendar.nextBusinessDay), day("2026-10-26"));
      w.client.send(completeTask, { taskId: "task-1" });
      const open = w.client.call(tasks, { filter: "open" });
      const completed = w.client.call(tasks, { filter: "completed" });
      const all = w.client.call(tasks, { filter: "all" });
      return { open, completed, all };
    },
    then: ({ open, completed, all }) => {
      const eggsRow = { taskId: "task-2", title: "Buy eggs", dueAt: null, completedAt: null };
      const doneMilk = { ...milkRow, completedAt: "2026-10-25T10:00:00+09:00" };
      return [
        answered(open, fulfilled({ tasks: [eggsRow] })),
        answered(completed, fulfilled({ tasks: [doneMilk] })),
        answered(all, fulfilled({ tasks: [doneMilk, eggsRow] })),
      ];
    },
  },
);

export const reopenCompleted = scenario("Complete a task and reopen it; tasks with filter open returns the task", {
  given: noTasks,
  when: (w) => {
    addMilk(w);
    w.clock.at("2026-10-25T10:01:00+09:00");
    w.client.send(completeTask, { taskId: "task-1" });
    const reopen = w.client.send(reopenTask, { taskId: "task-1" });
    const open = w.client.call(tasks, { filter: "open" });
    return { reopen, open };
  },
  then: ({ reopen, open }) => [
    answered(reopen, accepted),
    emitted(reopen, [event(taskReopened, { taskId: "task-1" })]),
    answered(open, fulfilled({ tasks: [milkRow] })),
  ],
});

export const rejectsReopenOpen = scenario("Reopen an open task; todo rejects reopenTask by requires completed", {
  given: noTasks,
  when: (w) => {
    addMilk(w);
    const reopen = w.client.send(reopenTask, { taskId: "task-1" });
    return { reopen };
  },
  then: ({ reopen }) => [answered(reopen, requires("completed"))],
});

export const skipsPassedReminderOnReopen = scenario(
  "Complete a task and reopen it after its reminder time passes; todo does not remind the user of the task",
  {
    given: noTasks,
    when: (w) => {
      addMilk(w);
      w.client.send(completeTask, { taskId: "task-1" });
      const morning = w.clock.at("2026-10-26T09:00:00+09:00");
      const reopen = w.client.send(reopenTask, { taskId: "task-1" });
      const detail = w.client.call(taskDetail, { taskId: "task-1" });
      return { morning, reopen, detail };
    },
    then: ({ morning, reopen, detail }) => [
      requested(morning, []),
      requested(reopen, []),
      answered(detail, fulfilled({ task: { ...milkDetail, remindAt: null } })),
    ],
  },
);

export const remindsReopenedAtReminder = scenario(
  "Complete a task and reopen it before its reminder time; todo reminds the user of the task at the reminder time",
  {
    given: noTasks,
    when: (w) => {
      addMilk(w);
      w.client.send(completeTask, { taskId: "task-1" });
      w.client.send(reopenTask, { taskId: "task-1" });
      const midnight = w.clock.at("2026-10-26T00:00:00+09:00");
      w.peer.device.leaveUnanswered(midnight.request(device.showNotification));
      return { midnight };
    },
    then: ({ midnight }) => [requested(midnight, [showMilk])],
  },
);

export const deletesTask = scenario("Delete a task; tasks no longer returns the task, and taskDetail returns null", {
  given: noTasks,
  when: (w) => {
    addMilk(w);
    const del = w.client.send(deleteTask, { taskId: "task-1" });
    const all = w.client.call(tasks, { filter: "all" });
    const detail = w.client.call(taskDetail, { taskId: "task-1" });
    return { del, all, detail };
  },
  then: ({ del, all, detail }) => [
    emitted(del, [event(taskDeleted, { taskId: "task-1" })]),
    answered(all, fulfilled({ tasks: [] })),
    answered(detail, fulfilled({ task: null })),
  ],
});

export const rejectsPastDue = scenario(
  "Change the due date of a task to a past time; todo rejects changeDue by requires notPast",
  {
    given: noTasks,
    when: (w) => {
      addMilk(w);
      const change = w.client.send(changeDue, { taskId: "task-1", dueAt: "2026-10-25T09:00:00+09:00" });
      return { change };
    },
    then: ({ change }) => [answered(change, requires("notPast"))],
  },
);

export const remindAtRemindAt = scenario("Let the reminder time of a task arrive; todo reminds the user of the task", {
  given: noTasks,
  when: (w) => {
    addMilk(w);
    const before = w.clock.at("2026-10-25T23:59:59+09:00");
    const midnight = w.clock.at("2026-10-26T00:00:00+09:00");
    w.peer.device.leaveUnanswered(midnight.request(device.showNotification));
    return { before, midnight };
  },
  then: ({ before, midnight }) => [requested(before, []), requested(midnight, [showMilk])],
});

export const remindsAfterNotShown = scenario(
  "Let device fail to show a reminder, and let the reminder time of the next task arrive; todo reminds the user of that task",
  {
    given: noTasks,
    when: (w) => {
      addMilk(w);
      const eggs = w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
      w.peer.calendar.answer(eggs.request(calendar.nextBusinessDay), day("2026-10-27"));
      const first = w.clock.at("2026-10-26T00:00:00+09:00");
      w.peer.device.answer(first.request(device.showNotification), unavailable);
      const second = w.clock.at("2026-10-27T00:00:00+09:00");
      w.peer.device.answer(second.request(device.showNotification), accepted);
      return { first, second };
    },
    then: ({ first, second }) => [
      requested(first, [showMilk]),
      requested(second, [request(device.showNotification, { text: "Buy eggs" })]),
    ],
  },
);

export const answersSubscriptions = scenario(
  "Subscribe to tasks and taskDetail, and complete a task; todo sends a new answer for each subscription whose answer changes",
  {
    given: noTasks,
    when: (w) => {
      addMilk(w);
      const openTasks = w.client.subscribe(tasks, { filter: "open" });
      const milk = w.client.subscribe(taskDetail, { taskId: "task-1" });
      w.client.send(completeTask, { taskId: "task-1" });
      w.client.unsubscribe(openTasks);
      w.client.unsubscribe(milk);
      return { openTasks, milk };
    },
    then: ({ openTasks, milk }) => [
      answered(openTasks, [fulfilled({ tasks: [milkRow] }), fulfilled({ tasks: [] })]),
      answered(milk, [fulfilled({ task: milkDetail }), fulfilled({ task: { ...milkDetail, isCompleted: true } })]),
    ],
  },
);

export const completeRedelivered = scenario(
  "Send completeTask twice with the same command id; todo does not process the second and returns the first answer",
  {
    given: noTasks,
    when: (w) => {
      addMilk(w);
      const first = w.client.send(completeTask, { taskId: "task-1" });
      const again = w.client.resend(first);
      return { first, again };
    },
    then: ({ first, again }) => [
      answered(first, accepted),
      emitted(first, [event(taskCompleted, { taskId: "task-1" })]),
      answered(again, accepted),
      emitted(again, []),
    ],
  },
);

export const remindAddedWhileAsking = scenario(
  "Add a task while todo asks calendar for the next business day; todo also asks for the added task without waiting for the answer",
  {
    given: noTasks,
    when: (w) => {
      const milk = addMilkUnanswered(w);
      const eggs = w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
      w.peer.calendar.answer(milk.request(calendar.nextBusinessDay), day("2026-10-26"));
      w.peer.calendar.answer(eggs.request(calendar.nextBusinessDay), day("2026-10-26"));
      return { eggs };
    },
    then: ({ eggs }) => [requested(eggs, [request(calendar.nextBusinessDay, { from: "2026-10-25" })])],
  },
);

export const remindInAnswerOrder = scenario(
  "Add two tasks, and let the answer for the second arrive first; todo sets the reminder time of the second task first",
  {
    given: noTasks,
    when: (w) => {
      const milk = addMilkUnanswered(w);
      w.clock.at("2026-10-26T10:05:00+09:00");
      const eggs = w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
      w.peer.calendar.answer(eggs.request(calendar.nextBusinessDay), day("2026-10-27"));
      const eggsDetail = w.client.call(taskDetail, { taskId: "task-2" });
      w.peer.calendar.answer(milk.request(calendar.nextBusinessDay), unavailable);
      const milkDetailAfter = w.client.call(taskDetail, { taskId: "task-1" });
      return { eggs, eggsDetail, milkDetailAfter };
    },
    then: ({ eggs, eggsDetail, milkDetailAfter }) => [
      requested(eggs, [request(calendar.nextBusinessDay, { from: "2026-10-26" })]),
      answered(
        eggsDetail,
        fulfilled({
          task: {
            title: "Buy eggs",
            isCompleted: false,
            dueAt: null,
            createdAt: "2026-10-26T10:05:00+09:00",
            remindAt: "2026-10-27T00:00:00+09:00",
          },
        }),
      ),
      answered(milkDetailAfter, fulfilled({ task: { ...milkDetail, remindAt: null } })),
    ],
  },
);

export const skipsBusinessDayReminderWhenDisabled = scenario(
  "Turn reminders off, and let the reminder time set to the start of the next business day arrive; todo does not remind the user",
  {
    given: noTasks,
    when: (w) => {
      addMilk(w);
      w.client.send(changeReminders, { shouldRemind: false });
      const settings = w.client.call(reminderSettings, {});
      const midnight = w.clock.at("2026-10-26T00:00:00+09:00");
      return { settings, midnight };
    },
    then: ({ settings, midnight }) => [answered(settings, fulfilled({ shouldRemind: false })), requested(midnight, [])],
  },
);

export const skipsDueReminderWhenDisabled = scenario(
  "Turn reminders off, change the due date of a task, and let the due date arrive; todo sets the reminder time to the due date but does not remind the user",
  {
    given: noTasks,
    when: (w) => {
      addMilk(w);
      w.client.send(changeReminders, { shouldRemind: false });
      w.client.send(changeDue, { taskId: "task-1", dueAt: "2026-10-27T18:00:00+09:00" });
      const due = w.clock.at("2026-10-27T18:00:00+09:00");
      return { due };
    },
    then: ({ due }) => [requested(due, [])],
  },
);

export const remindsWhenReenabled = scenario(
  "Turn reminders off and back on before the reminder time; todo reminds the user at the reminder time",
  {
    given: noTasks,
    when: (w) => {
      addMilk(w);
      w.client.send(changeReminders, { shouldRemind: false });
      w.client.send(changeReminders, { shouldRemind: true });
      const midnight = w.clock.at("2026-10-26T00:00:00+09:00");
      w.peer.device.leaveUnanswered(midnight.request(device.showNotification));
      return { midnight };
    },
    then: ({ midnight }) => [requested(midnight, [showMilk])],
  },
);

export const rejectsMalformedTitle = scenario(
  "Add a task whose title is not a string; todo rejects addTask as invalid-input",
  {
    given: noTasks,
    when: (w) => {
      const add = w.client.send(addTask, { taskId: "task-1", title: unchecked(7) });
      return { add };
    },
    then: ({ add }) => [answered(add, { result: "rejected", rejection: { kind: "invalid-input" } })],
  },
);

export const rejectsMissingTask = scenario(
  "Complete and reopen a task that does not exist; todo rejects completeTask and reopenTask as not-found",
  {
    given: noTasks,
    when: (w) => {
      const complete = w.client.send(completeTask, { taskId: "task-9" });
      const reopen = w.client.send(reopenTask, { taskId: "task-9" });
      return { complete, reopen };
    },
    then: ({ complete, reopen }) => [
      answered(complete, { result: "rejected", rejection: { kind: "not-found" } }),
      answered(reopen, { result: "rejected", rejection: { kind: "not-found" } }),
    ],
  },
);

export const renamesTask = scenario("Rename a task; taskDetail returns the new title", {
  given: noTasks,
  when: (w) => {
    addMilk(w);
    w.client.send(renameTask, { taskId: "task-1", title: "Buy soy milk" });
    const detail = w.client.call(taskDetail, { taskId: "task-1" });
    return { detail };
  },
  then: ({ detail }) => [answered(detail, fulfilled({ task: { ...milkDetail, title: "Buy soy milk" } }))],
});

export const asksBusinessDayAgainOnStart = scenario(
  "Restart the server while todo asks calendar for the next business day; todo asks again for each task whose reminder time is pending",
  {
    given: noTasks,
    when: (w) => {
      const add = addMilkUnanswered(w);
      // The restart drops the waiting request, which calendar never answers.
      w.peer.calendar.leaveUnanswered(add.request(calendar.nextBusinessDay));
      w.clock.at("2026-10-25T10:05:00+09:00");
      const restart = w.host.restart();
      w.peer.calendar.answer(restart.request(calendar.nextBusinessDay), day("2026-10-26"));
      const detail = w.client.call(taskDetail, { taskId: "task-1" });
      return { restart, detail };
    },
    then: ({ restart, detail }) => [
      requested(restart, [request(calendar.nextBusinessDay, { from: "2026-10-25" })]),
      answered(detail, fulfilled({ task: milkDetail })),
    ],
  },
);
