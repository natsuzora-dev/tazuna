import { contract } from "@natsuzora-dev/tazuna";
import { addTask, taskCount } from "./todo.ts";

export const todo = contract({ addTask, taskCount });
