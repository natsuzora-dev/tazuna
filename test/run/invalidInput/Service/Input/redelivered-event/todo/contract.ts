import { ref } from "@natsuzora-dev/tazuna";
import { addTask, contract, removeTask, Task, taskAdded, taskRemoved } from "./todo.ts";

export const todo = contract({ TaskId: ref(Task), addTask, taskAdded, removeTask, taskRemoved });
