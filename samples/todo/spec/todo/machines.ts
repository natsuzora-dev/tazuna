import { instant, ref } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { recordReminderDecisionFailed, recordReminderTimeReached, setReminder } from "./commands.ts";
import { machine, Task } from "./data.ts";
import { dueChanged } from "./events.ts";

export const reminder = machine({
  description:
    "Wait until the reminder time of each open task arrives, entering waiting again when the due date moves the reminder time",
  receives: { dueChanged },
  commands: { recordReminderTimeReached },
  initial: "reminding",
  states: {
    reminding: {
      type: "map",
      key: { taskId: ref(Task) },
      initial: "waiting",
      states: { waiting: { held: { remindAt: instant } }, recording: {} },
    },
  },
}).chart({
  states: {
    reminding: {
      items: ({ records }) =>
        records.Task.filter((t) => t.completedAt === null && t.remindAt !== null).map((t) => ({ taskId: t.id })),
      initial: { with: { remindAt: ({ key, records }) => records.Task.get(key.taskId)?.remindAt ?? null } },
    },
    waiting: {
      on: {
        dueChanged: [
          {
            guard: { sameTask: ({ key, payload }) => payload.id === key.taskId },
            target: "waiting",
            reenter: true,
            with: { remindAt: ({ key, records }) => records.Task.get(key.taskId)?.remindAt ?? null },
          },
        ],
      },
      after: { reminderTime: { at: ({ held }) => held.remindAt, onFired: [{ target: "recording" }] } },
    },
    recording: {
      sends: { recordReminderTimeReached: { input: ({ key }) => key, onAccepted: [], onRejected: [] } },
    },
  },
});

export const businessDayReminder = machine({
  description:
    "Set the reminder time of each task whose reminder time is pending to the start of the next business day",
  queries: { nextBusinessDay: calendar.nextBusinessDay },
  commands: { setReminder, recordReminderDecisionFailed },
  initial: "deciding",
  states: {
    deciding: {
      type: "map",
      key: { taskId: ref(Task) },
      initial: "asking",
      states: { asking: {}, scheduling: { held: { startsAt: instant } }, failing: {} },
    },
  },
}).chart({
  states: {
    deciding: {
      items: ({ records }) =>
        records.Task.filter((t) => t.reminderDecision === "pending").map((t) => ({ taskId: t.id })),
    },
    asking: {
      calls: {
        nextBusinessDay: {
          input: ({ now }) => ({ after: now }),
          onFulfilled: [{ target: "scheduling", with: { startsAt: ({ output }) => output.startsAt } }],
          onRejected: [{ target: "failing" }],
        },
      },
    },
    scheduling: {
      sends: {
        setReminder: {
          input: ({ key, held }) => ({ taskId: key.taskId, remindAt: held.startsAt }),
          onAccepted: [],
          onRejected: [],
        },
      },
    },
    failing: {
      sends: {
        recordReminderDecisionFailed: { input: ({ key }) => key, onAccepted: [], onRejected: [] },
      },
    },
  },
});
