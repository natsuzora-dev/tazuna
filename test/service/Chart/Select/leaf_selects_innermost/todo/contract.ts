import { addTask, contract, pickTask, reminded } from "./todo.ts";

export const todo = contract({ addTask, pickTask, reminded });
