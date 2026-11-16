import { book, booked, contract, holiday } from "./calendar.ts";

export const calendar = contract({ holiday, booked, book });
