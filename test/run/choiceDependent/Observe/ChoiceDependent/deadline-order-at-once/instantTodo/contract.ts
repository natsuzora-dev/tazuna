import { contract } from "@natsuzora-dev/tazuna";
import { addTask, reminded } from "./instantTodo.ts";

export const instantTodo = contract({ addTask, reminded });
