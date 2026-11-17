import { automation, count, counted, log, logged, schedule, taskAdded } from "./todo.ts";

export const logAdded = automation({
  receives: { taskAdded },
  commands: { log },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });

export const countLogged = automation({
  receives: { logged },
  commands: { count },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });

export const scheduleCounted = automation({
  receives: { counted },
  commands: { schedule },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });
