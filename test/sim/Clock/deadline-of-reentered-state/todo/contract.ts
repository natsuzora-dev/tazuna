import { addTask, contract, reminded } from "./todo.ts";

export const todo = contract({ addTask, reminded });
