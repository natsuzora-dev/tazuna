import { contract } from "@natsuzora-dev/tazuna";
import { addReminder } from "./reminders.ts";

export const reminders = contract({ addReminder });
