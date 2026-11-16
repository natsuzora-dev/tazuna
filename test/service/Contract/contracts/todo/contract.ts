import { addTask, contract, pinTask, pinTaskByTitle, renameTask, taskTitles } from "./todo.ts";

export const todo = contract({ addTask, renameTask, pinTask, pinTaskByTitle, taskTitles });
