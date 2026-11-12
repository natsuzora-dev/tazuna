import { contract } from "@natsuzora-dev/tazuna";
import { completeTask, task } from "./todo.ts";

export const todo = contract({ completeTask, task });
