import { contract } from "@natsuzora-dev/tazuna";
import { book, booked, cancel, cancelled, nextDay, reserve } from "./calendar.ts";

export const calendar = contract({ nextDay, book, booked, cancel, cancelled, reserve });
