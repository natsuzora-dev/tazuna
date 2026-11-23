import { addTask, completeTask, contract, reopenTask } from "./todo.ts";

export const todo = contract({ addTask, completeTask, reopenTask });
