import { addTask, contract, taskAdded } from "./todo.ts";

export const todo = contract({ addTask, taskAdded });
