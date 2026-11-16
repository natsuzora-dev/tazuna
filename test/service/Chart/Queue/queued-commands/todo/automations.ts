import { archive, automation, count, log, logged, taskAdded } from "./todo.ts";

export const logAdded = automation({
  receives: { taskAdded },
  commands: { log },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });

export const countAdded = automation({
  receives: { taskAdded },
  commands: { count },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });

export const archiveLogged = automation({
  receives: { logged },
  commands: { archive },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });
