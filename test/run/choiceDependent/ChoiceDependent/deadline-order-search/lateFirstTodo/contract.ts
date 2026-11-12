import { contract } from "@natsuzora-dev/tazuna";
import { addTask, reminded } from "./lateFirstTodo.ts";

export const lateFirstTodo = contract({ addTask, reminded });
