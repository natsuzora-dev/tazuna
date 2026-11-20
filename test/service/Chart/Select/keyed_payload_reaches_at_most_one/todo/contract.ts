import { completeTask, contract, openTasks, tasks } from "./todo.ts";

export const todo = contract({ completeTask, tasks, openTasks });
