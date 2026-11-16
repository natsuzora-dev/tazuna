import { contract } from "@natsuzora-dev/tazuna";
import { markSeen, taskAdded, tasks } from "./todo.ts";

export const todo = contract({ markSeen, taskAdded, tasks });
