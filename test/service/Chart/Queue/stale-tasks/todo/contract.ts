import { addTask, archiveTask, contract, dropTask, finishTask } from "./todo.ts";

export const todo = contract({ addTask, finishTask, archiveTask, dropTask });
