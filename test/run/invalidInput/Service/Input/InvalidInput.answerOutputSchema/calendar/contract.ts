import { book, contract, holiday, nextDay } from "./calendar.ts";

export const calendar = contract({ nextDay, holiday, book });
