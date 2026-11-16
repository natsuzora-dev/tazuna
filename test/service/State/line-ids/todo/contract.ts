import { contract } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const todo = contract({ addTask });
