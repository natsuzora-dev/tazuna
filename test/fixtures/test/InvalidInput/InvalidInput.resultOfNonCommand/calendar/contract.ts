import { contract, dayChanged, nextDay } from "./calendar.ts";

export const calendar = contract({ nextDay, dayChanged });
