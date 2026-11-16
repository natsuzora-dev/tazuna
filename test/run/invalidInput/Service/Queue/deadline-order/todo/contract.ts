import { addTask, completeTask, contract, followedUp, reminded } from "./todo.ts";

export const todo = contract({ addTask, completeTask, reminded, followedUp });
