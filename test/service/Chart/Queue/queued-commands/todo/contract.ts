import { contract } from "@natsuzora-dev/tazuna";
import { addTask, counted, logged, scheduled, taskAdded } from "./todo.ts";

export const todo = contract({ addTask, taskAdded, logged, counted, scheduled });
