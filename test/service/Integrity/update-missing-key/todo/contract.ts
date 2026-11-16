import { contract } from "@natsuzora-dev/tazuna";
import { renameTask, taskCount } from "./todo.ts";

export const todo = contract({ renameTask, taskCount });
