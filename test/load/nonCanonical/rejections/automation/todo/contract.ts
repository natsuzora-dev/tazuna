import { contract } from "@natsuzora-dev/tazuna";
import { addTask, taskAdded } from "./todo.ts";

export const todo = contract({ addTask, taskAdded });
