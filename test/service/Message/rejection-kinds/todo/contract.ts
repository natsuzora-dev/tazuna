import { contract } from "@natsuzora-dev/tazuna";
import { addTask, completeTask, swapTitles, titledCount } from "./todo.ts";

export const todo = contract({ addTask, completeTask, swapTitles, titledCount });
