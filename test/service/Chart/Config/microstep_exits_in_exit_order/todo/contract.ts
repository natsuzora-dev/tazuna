import { addTask, completeTask, contract, removeTask, renameTask, stepsRecorded } from "./todo.ts";

export const todo = contract({ addTask, completeTask, removeTask, renameTask, stepsRecorded });
