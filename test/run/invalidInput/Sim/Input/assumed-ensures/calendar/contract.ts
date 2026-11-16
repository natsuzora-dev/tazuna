import { contract } from "@natsuzora-dev/tazuna";
import { addReminder, nextDay, reminderAdded, reminderRemoved, removeReminder } from "./calendar.ts";

export const calendar = contract({ nextDay, reminderAdded, addReminder, reminderRemoved, removeReminder });
