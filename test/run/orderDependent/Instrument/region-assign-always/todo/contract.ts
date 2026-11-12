import { contract } from "@natsuzora-dev/tazuna";
import { addTask, clearTasks } from "./todo.ts";

export const todo = contract({ addTask, clearTasks });
