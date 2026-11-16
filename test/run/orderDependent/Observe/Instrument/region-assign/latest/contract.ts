import { contract } from "@natsuzora-dev/tazuna";
import { addTask, clearTasks } from "./latest.ts";

export const latest = contract({ addTask, clearTasks });
