import { service } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";

export const { machine, scenario } = service({ name: "cleanup", description: "Clean up reminders" });

export const remover = machine({
  description: "Remove a reminder",
  commands: { removeReminder: calendar.removeReminder },
  initial: "removing",
  states: { removing: {}, done: { type: "final" } },
}).chart({
  states: {
    removing: { sends: { removeReminder: { onAccepted: [{ target: "done" }], onRejected: [{ target: "done" }] } } },
  },
});
