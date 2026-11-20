import { book, bookingConfirmed, contract, slotFreed } from "./calendar.ts";

export const calendar = contract({ book, bookingConfirmed, slotFreed });
