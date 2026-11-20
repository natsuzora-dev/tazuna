import { addTask, completeTask, contract, swapTitles, titledCount } from "./todo.ts";

export const todo = contract({ addTask, completeTask, swapTitles, titledCount });
