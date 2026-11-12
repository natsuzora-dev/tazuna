import { contract } from "@natsuzora-dev/tazuna";
import { taskAdded as addedCount } from "./queries.ts";
import { addTask, taskAdded } from "./todo.ts";

export const todo = contract({ addTask, taskAdded, addedCount });
