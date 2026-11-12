import { contract } from "@natsuzora-dev/tazuna";
import { saveTask, tasks } from "./todo.ts";

export const todo = contract({ saveTask, tasks });
