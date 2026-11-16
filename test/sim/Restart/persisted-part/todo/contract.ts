import { addTask, contract, taskCount } from "./todo.ts";

export const todo = contract({ addTask, taskCount });
