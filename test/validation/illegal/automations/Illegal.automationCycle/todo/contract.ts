import { add, build, run } from "./commands.ts";
import { contract } from "./data.ts";
import { added } from "./events.ts";

export const todo = contract({ added, add, build, run });
