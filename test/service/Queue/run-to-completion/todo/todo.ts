import { datetime, emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { automation, command, event, contract } = service({ description: "Keep tasks" });

export const taskAdded = event({ payload: { taskId: z.string(), addedAt: datetime } });
export const logged = event({
  payload: { taskId: z.string(), loggedAt: datetime },
});

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input, now }) => [emit(taskAdded, { taskId: input.taskId, addedAt: now })]);

export const log = command({
  input: { taskId: z.string() },
  emits: [logged],
}).decide(({ input, now }) => [emit(logged, { taskId: input.taskId, loggedAt: now })]);

export const logAdded = automation({
  receives: { taskAdded },
  commands: { log },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });
