import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { calendar } from "../calendar/contract.ts";
import { device } from "../device/contract.ts";

export const Reminder = entity({ description: "A reminder", fields: { id: z.string() }, key: "id" });

export const { command, machine, createEvent, contract } = service({
  description: "Keep the reminders",
  entities: { Reminder },
});

export const reminderAdded = createEvent({ entity: Reminder });

export const addReminder = command({
  input: { reminderId: Reminder.fields.id },
  emits: [reminderAdded],
}).decide(({ input }) => [emit(reminderAdded, { id: input.reminderId })]);

export const scheduler = machine({
  description: "Ask for the next day of each reminder, then show a notification of the reminder",
  queries: { nextDay: calendar.nextDay },
  commands: { showNotification: device.showNotification },
  initial: "scheduling",
  states: {
    scheduling: {
      type: "map",
      key: { reminderId: ref(Reminder) },
      initial: "asking",
      states: { asking: {}, notifying: {}, done: {} },
    },
  },
}).chart({
  states: {
    scheduling: { items: ({ records }) => records.Reminder.map((r) => ({ reminderId: r.id })) },
    asking: {
      calls: {
        nextDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "notifying" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
    notifying: {
      sends: {
        showNotification: {
          input: ({ key }) => ({ text: key.reminderId }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});
