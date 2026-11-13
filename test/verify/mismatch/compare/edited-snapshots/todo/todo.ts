import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event } = service({ description: "Keep tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);
