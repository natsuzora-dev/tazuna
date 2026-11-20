import { addDoneTask, addTask, completeTask, contract } from "./todo.ts";

export const todo = contract({ addTask, completeTask, addDoneTask });
