import { clearAll, contract, notified, starTask } from "./reminders.ts";

export const reminders = contract({ starTask, clearAll, notified });
