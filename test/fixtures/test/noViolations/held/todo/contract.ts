import { addTask, contract, openLabels, pressRemind, renameTask, selectTask } from "./todo.ts";

export const todo = contract({ addTask, renameTask, selectTask, pressRemind, openLabels });
