import { contract, renameTask, taskCount } from "./todo.ts";

export const todo = contract({ renameTask, taskCount });
