import { contract } from "@natsuzora-dev/tazuna";
import { addTasks } from "./todo.ts";

export const todo = contract({ addTasks });
