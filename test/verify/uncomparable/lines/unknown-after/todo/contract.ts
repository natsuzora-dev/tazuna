import { contract } from "@natsuzora-dev/tazuna";
import { addTask, taskAdded, taskCountChanged } from "./todo.ts";

export const todo = contract({ addTask, taskAdded, taskCountChanged });
