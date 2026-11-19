import { addTask, contract, counted, logged, scheduled, taskAdded } from "./todo.ts";

export const todo = contract({ addTask, taskAdded, logged, counted, scheduled });
