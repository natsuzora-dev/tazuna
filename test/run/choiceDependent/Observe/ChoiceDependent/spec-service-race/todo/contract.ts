import { closeTask, completeTask, contract } from "./todo.ts";

export const todo = contract({ completeTask, closeTask });
