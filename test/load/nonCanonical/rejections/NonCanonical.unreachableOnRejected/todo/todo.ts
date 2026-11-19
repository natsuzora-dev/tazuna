import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { automation, command, event, contract } = service({ name: "todo", description: "Keep the tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const taskCounted = event({ payload: { taskId: z.string() } });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const countTask = command({
  input: { taskId: z.string() },
  emits: [taskCounted],
}).decide(({ input }) => [emit(taskCounted, { taskId: input.taskId })]);

export const countAdded = automation({
  receives: { taskAdded },
  commands: { countTask },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }), onRejected: [] });

export const todo = contract({ addTask, taskAdded, taskCounted });
