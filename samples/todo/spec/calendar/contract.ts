import { contract } from "./data.ts";
import { nextBusinessDay } from "./queries.ts";

export const calendar = contract({ nextBusinessDay });
