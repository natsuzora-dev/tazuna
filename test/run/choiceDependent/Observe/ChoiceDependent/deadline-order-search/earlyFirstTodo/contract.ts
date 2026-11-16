import { contract } from "@natsuzora-dev/tazuna";
import { addTask, reminded } from "./earlyFirstTodo.ts";

export const earlyFirstTodo = contract({ addTask, reminded });
