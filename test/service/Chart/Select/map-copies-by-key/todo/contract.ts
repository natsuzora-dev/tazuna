import { contract } from "@natsuzora-dev/tazuna";
import { completeTask, openTasks, tasks } from "./todo.ts";

export const todo = contract({ completeTask, tasks, openTasks });
