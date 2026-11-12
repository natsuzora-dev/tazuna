import { contract, ref } from "@natsuzora-dev/tazuna";
import { addTask, Task, taskAdded } from "./todo.ts";

export const todo = contract({ TaskId: ref(Task), taskAdded, addTask });
