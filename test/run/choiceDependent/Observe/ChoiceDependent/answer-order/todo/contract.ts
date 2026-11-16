import { contract, saveTask, tasks } from "./todo.ts";

export const todo = contract({ saveTask, tasks });
