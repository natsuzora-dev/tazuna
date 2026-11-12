import { contract } from "@natsuzora-dev/tazuna";
import { add, build, run } from "./commands.ts";
import { added } from "./events.ts";

export const todo = contract({ added, add, build, run });
