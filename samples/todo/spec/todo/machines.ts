import { date, datetime, ref } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { recordReminderDecisionFailed, recordReminderTimeReached, setReminder } from "./commands.ts";
import { machine, Task, todoConstants } from "./data.ts";

export const reminder = machine({
  description: "Wait until the reminder time of each open task arrives",
  commands: { recordReminderTimeReached },
  initial: "reminding",
  states: {
    reminding: {
      type: "map",
      key: { taskId: ref(Task) },
      initial: "waiting",
      states: { waiting: { after: ["reminderTime"], held: { remindAt: datetime } }, recording: {} },
    },
  },
}).chart({
  states: {
    reminding: {
      items: ({ records }) =>
        records.Task.filter((t) => t.completedAt === null && t.remindAt !== null).map((t) => ({ taskId: t.id })),
    },
    waiting: {
      holds: { remindAt: ({ key, records }) => records.Task.get(key.taskId)?.remindAt ?? null },
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
      context: { day: date.nullable().default(null) },
      initial: "asking",
      states: { asking: {}, scheduling: { held: { day: date } }, failing: {} },
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
          input: ({ now }) => ({ from: now.toZonedDateTimeISO(todoConstants.timeZone).toPlainDate() }),
          onFulfilled: [{ target: "scheduling", assign: { day: ({ output }) => output.day } }],
          onRejected: [{ target: "failing" }],
        },
      },
    },
    scheduling: {
      holds: { day: ({ context }) => context.day },
      sends: {
        setReminder: {
          input: ({ key, held }) => ({
            taskId: key.taskId,
            remindAt: held.day.toZonedDateTime(todoConstants.timeZone).toInstant(),
          }),
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
