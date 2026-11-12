import { contract } from "@natsuzora-dev/tazuna";
import { addTask, tasksNamed } from "./todo.ts";

export const todo = contract({ addTask, tasksNamed });
