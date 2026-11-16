import { contract } from "@natsuzora-dev/tazuna";
import { addTask, reminded } from "./todo.ts";

export const todo = contract({ addTask, reminded });
