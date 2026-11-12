import { contract, ref } from "@natsuzora-dev/tazuna";
import { taskCard, taskNote } from "./queries.ts";
import { addTask, completeTask, Task, taskCompleted } from "./todo.ts";

export const todo = contract({ TaskId: ref(Task), addTask, completeTask, taskCompleted, taskCard, taskNote });
