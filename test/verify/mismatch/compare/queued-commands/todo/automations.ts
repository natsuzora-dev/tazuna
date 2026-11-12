import { automation, count, log, schedule, taskAdded } from "./todo.ts";

export const logAdded = automation({
  receives: { taskAdded },
  commands: { log },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });

export const countAdded = automation({
  receives: { taskAdded },
  commands: { count },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });

export const scheduleAdded = automation({
  receives: { taskAdded },
  commands: { schedule },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });
