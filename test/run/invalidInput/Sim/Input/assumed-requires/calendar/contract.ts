import { contract } from "@natsuzora-dev/tazuna";
import { book, booked, holiday } from "./calendar.ts";

export const calendar = contract({ holiday, booked, book });
