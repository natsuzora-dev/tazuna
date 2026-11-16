import { contract } from "@natsuzora-dev/tazuna";
import { holiday, nextDay } from "./calendar.ts";

export const calendar = contract({ nextDay, holiday });
