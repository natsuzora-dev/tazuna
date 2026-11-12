import { contract } from "@natsuzora-dev/tazuna";
import { closeTask, completeTask } from "./todo.ts";

export const todo = contract({ completeTask, closeTask });
