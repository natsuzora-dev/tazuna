import { addTask, contract, hasTasks, taskCount, taskIds } from "./todo.ts";

export const todo = contract({ addTask, taskIds, taskCount, hasTasks });
