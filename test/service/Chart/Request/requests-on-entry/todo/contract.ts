import { contract } from "@natsuzora-dev/tazuna";
import { addDoneTask, addTask, completeTask } from "./todo.ts";

export const todo = contract({ addTask, completeTask, addDoneTask });
