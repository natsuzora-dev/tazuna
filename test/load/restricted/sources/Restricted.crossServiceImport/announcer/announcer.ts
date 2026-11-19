import { emit, service } from "@natsuzora-dev/tazuna";
import { Task } from "../todo/todo.ts";

export const { command, event, contract } = service({
  name: "announcer",
  description: "Announce tasks, importing the todo entity from a file of todo",
});

export const announced = event({ payload: { taskId: Task.fields.id } });

export const announce = command({
  input: { taskId: Task.fields.id },
  emits: [announced],
}).decide(({ input }) => [emit(announced, { taskId: input.taskId })]);

export const announcer = contract({ announce, announced });
