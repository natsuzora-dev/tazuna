import { addReminder, contract, nextDay, reminderAdded, reminderRemoved, removeReminder } from "./calendar.ts";

export const calendar = contract({ nextDay, reminderAdded, addReminder, reminderRemoved, removeReminder });
