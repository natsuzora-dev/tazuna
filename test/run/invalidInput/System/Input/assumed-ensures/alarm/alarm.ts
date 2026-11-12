import { service } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";

export const { machine } = service({ description: "Remind of the tasks" });

export const reminder = machine({
  description: "Add a reminder",
  commands: { addReminder: calendar.addReminder },
  initial: "adding",
  states: { adding: {}, done: { type: "final" } },
}).chart({
  states: {
    adding: { sends: { addReminder: { onAccepted: [{ target: "done" }], onRejected: [{ target: "done" }] } } },
  },
});
