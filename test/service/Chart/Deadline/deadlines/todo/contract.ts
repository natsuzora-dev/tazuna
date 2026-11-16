import { contract } from "@natsuzora-dev/tazuna";
import { addTask, completeTask, followedUp, reminded } from "./todo.ts";

export const todo = contract({ addTask, completeTask, reminded, followedUp });
