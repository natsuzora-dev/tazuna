import { contract } from "@natsuzora-dev/tazuna";
import { addTask, completeTask, reopenTask } from "./todo.ts";

export const todo = contract({ addTask, completeTask, reopenTask });
