import { addTask, completeTask, contract, openRows, signal, tasks } from "./todo.ts";

export const todo = contract({ addTask, completeTask, signal, tasks, openRows });
