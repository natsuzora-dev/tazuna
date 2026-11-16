import { contract } from "@natsuzora-dev/tazuna";
import { addTask, openLabels, pressRemind, renameTask, selectTask } from "./todo.ts";

export const todo = contract({ addTask, renameTask, selectTask, pressRemind, openLabels });
