import { addTask, contract, taskAdded, taskCount } from "./todo.ts";

export const todo = contract({ addTask, taskAdded, taskCount });
