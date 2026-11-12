import { contract } from "@natsuzora-dev/tazuna";
import { addTask } from "./uncheckedPlanTodo.ts";

export const uncheckedPlanTodo = contract({ addTask });
