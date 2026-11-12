import { contract } from "@natsuzora-dev/tazuna";
import { addTask, completeTask, removeTask, renameTask, stepsRecorded } from "./todo.ts";

export const todo = contract({ addTask, completeTask, removeTask, renameTask, stepsRecorded });
