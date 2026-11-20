import { clearAll, contract, starTask } from "./reminders.ts";

export const reminders = contract({ starTask, clearAll });
