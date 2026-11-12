import { contract } from "@natsuzora-dev/tazuna";
import { book, holiday, nextDay } from "./calendar.ts";

export const calendar = contract({ nextDay, holiday, book });
