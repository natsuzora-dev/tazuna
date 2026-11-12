import { contract } from "@natsuzora-dev/tazuna";
import { addTask, hasTasks, taskCount, taskIds } from "./todo.ts";

export const todo = contract({ addTask, taskIds, taskCount, hasTasks });
