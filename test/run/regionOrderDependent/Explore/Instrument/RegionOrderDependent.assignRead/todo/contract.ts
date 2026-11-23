import { addTask, clearTasks, contract } from "./todo.ts";

export const todo = contract({ addTask, clearTasks });
