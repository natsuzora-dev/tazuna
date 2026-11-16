import { contract } from "@natsuzora-dev/tazuna";
import { addTask, completeTask, openRows, signal, tasks } from "./todo.ts";

export const todo = contract({ addTask, completeTask, signal, tasks, openRows });
