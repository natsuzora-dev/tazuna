import { contract } from "@natsuzora-dev/tazuna";
import { taskCount, tasks } from "./todo.ts";

export const todo = contract({ tasks, taskCount });
