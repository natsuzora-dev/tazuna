import { addTask, contract, note, taskCount } from "./todo.ts";

export const todo = contract({ addTask, note, taskCount });
