import { addReminder, contract, nextDay, reminderAdded } from "./calendar.ts";

export const calendar = contract({ nextDay, addReminder, reminderAdded });
