import { book, booked, cancel, cancelled, contract, move, nextDay, reserve } from "./calendar.ts";

export const calendar = contract({ nextDay, book, booked, cancel, cancelled, reserve, move });
