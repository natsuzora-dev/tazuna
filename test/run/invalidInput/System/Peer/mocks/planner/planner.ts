import { emit, service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { automation, command, event } = service({ description: "Plan tasks" });

export const planned = event({ payload: { taskId: todo.addTask.input.taskId, title: todo.addTask.input.title } });

export const plan = command({
  input: { taskId: todo.addTask.input.taskId, title: todo.addTask.input.title },
  emits: [planned],
}).decide(({ input }) => [emit(planned, { taskId: input.taskId, title: input.title })]);

export const addPlanned = automation({ receives: { planned }, commands: { addTask: todo.addTask } }).send({
  input: ({ payload }) => ({ taskId: payload.taskId, title: payload.title }),
  onRejected: [],
});
