import { contract } from "@natsuzora-dev/tazuna";
import { addTask, firstTaskPicked, pickFirstTask } from "./todo.ts";

export const todo = contract({ addTask, pickFirstTask, firstTaskPicked });
