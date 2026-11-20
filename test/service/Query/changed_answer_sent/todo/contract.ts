import { addTask, contract, hasTasks, isLate, taskCount, taskIds } from "./todo.ts";

export const todo = contract({ addTask, taskIds, taskCount, hasTasks, isLate });
