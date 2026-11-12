import { contract } from "@natsuzora-dev/tazuna";
import { addTask, pickTask, reminded } from "./todo.ts";

export const todo = contract({ addTask, pickTask, reminded });
