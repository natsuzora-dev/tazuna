import { ref } from "@natsuzora-dev/tazuna";
import { addTask, contract, Task, taskAdded } from "./todo.ts";

export const todo = contract({ TaskId: ref(Task), taskAdded, addTask });
