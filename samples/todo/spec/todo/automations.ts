import { device } from "../device/contract.ts";
import { automation } from "./data.ts";
import { reminderTimeReached } from "./events.ts";

export const reminderNotification = automation({
  receives: { reminderTimeReached },
  commands: { showNotification: device.showNotification },
}).send({
  guard: { remindersEnabled: ({ records }) => records.Settings.shouldRemind },
  input: ({ payload }) => ({ notice: { id: "reminder", values: { title: payload.title } } }),
  onRejected: [],
});
