import { contract } from "@natsuzora-dev/tazuna";
import { addTask, pinTask, pinTaskByTitle, renameTask, taskTitles } from "./todo.ts";

export const todo = contract({ addTask, renameTask, pinTask, pinTaskByTitle, taskTitles });
