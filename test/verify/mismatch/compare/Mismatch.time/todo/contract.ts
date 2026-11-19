import { addTask, contract, taskAdded, taskCountChanged } from "./todo.ts";

export const todo = contract({ addTask, taskAdded, taskCountChanged });
