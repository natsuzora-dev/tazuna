import { contract } from "@natsuzora-dev/tazuna";
import { addTask, taskAdded, taskCount } from "./todo.ts";

export const todo = contract({ addTask, taskAdded, taskCount });
