import { contract } from "@natsuzora-dev/tazuna";
import { addReminder, nextDay, reminderAdded } from "./calendar.ts";

export const calendar = contract({ nextDay, addReminder, reminderAdded });
