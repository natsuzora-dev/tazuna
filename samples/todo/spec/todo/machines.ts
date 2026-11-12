import { date, datetime, type RowOf, ref } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { recordReminderDecisionFailed, recordReminderTimeReached, setReminder } from "./commands.ts";
import { machine, Task, todoConstants } from "./data.ts";

type Tasks = { readonly Task: readonly RowOf<typeof Task>[] };

const nextRemindAt = (records: Tasks) =>
  records.Task.flatMap((t) => (t.completedAt === null && t.remindAt !== null ? [t.remindAt] : [])).toSorted(
    Temporal.Instant.compare,
  )[0] ?? null;
const scheduled = ({ records }: { readonly records: Tasks }) => nextRemindAt(records) !== null;
const nothingScheduled = (args: { readonly records: Tasks }) => !scheduled(args);

export const reminder = machine({
  description: "Wait until the reminder time of an open task arrives",
  commands: { recordReminderTimeReached },
  initial: "idle",
  states: { idle: {}, waiting: { held: { remindAt: datetime } }, recording: {} },
}).chart({
  states: {
    idle: { always: [{ guard: { scheduled }, target: "waiting" }] },
    waiting: {
      holds: { remindAt: ({ records }) => nextRemindAt(records) },
      always: [{ guard: { nothingScheduled }, target: "idle" }],
      after: { reminderTime: { at: ({ held }) => held.remindAt, onFired: [{ target: "recording" }] } },
    },
    recording: {
      sends: { recordReminderTimeReached: { onAccepted: [{ target: "idle" }], onRejected: [] } },
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
