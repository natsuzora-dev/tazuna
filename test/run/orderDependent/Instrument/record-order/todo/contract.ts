import { contract } from "@natsuzora-dev/tazuna";
import { addTask, titles, titlesInArray } from "./todo.ts";

export const todo = contract({ addTask, titles, titlesInArray });
