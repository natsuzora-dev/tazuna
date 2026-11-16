import { contract } from "@natsuzora-dev/tazuna";
import { addTask, archiveTask, dropTask, finishTask } from "./todo.ts";

export const todo = contract({ addTask, finishTask, archiveTask, dropTask });
