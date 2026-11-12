import { contract } from "@natsuzora-dev/tazuna";
import { clearAll, notified, starTask } from "./reminders.ts";

export const reminders = contract({ starTask, clearAll, notified });
