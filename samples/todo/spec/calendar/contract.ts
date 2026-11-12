import { contract } from "@natsuzora-dev/tazuna";
import { nextBusinessDay } from "./queries.ts";

export const calendar = contract({ nextBusinessDay });
