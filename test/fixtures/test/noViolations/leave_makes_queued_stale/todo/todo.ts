import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, machine, contract, scenario } = service({ name: "todo", description: "Keep tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const logged = event({ payload: { taskId: z.string() } });
export const noted = event({ payload: { taskId: z.string() } });

export const addTask = command({ callers: ["client"], input: { taskId: z.string() }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { taskId: input.taskId })],
);

export const log = command({ callers: ["client", "todo"], input: { taskId: z.string() }, emits: [logged] }).decide(
  ({ input }) => [emit(logged, { taskId: input.taskId })],
);

export const note = command({ callers: ["client", "todo"], input: { taskId: z.string() }, emits: [noted] }).decide(
  ({ input }) => [emit(noted, { taskId: input.taskId })],
);

export const logger = machine({
  description: "Log each added task, and note it once the log is accepted, unless logged arrives first",
  receives: { taskAdded, logged },
  commands: { log, note },
  initial: "idle",
  states: { idle: {}, logging: { held: { taskId: z.string() } }, noting: { held: { taskId: z.string() } } },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "logging", with: { taskId: ({ payload }) => payload.taskId } }] } },
    logging: {
      on: { logged: [{ target: "idle" }] },
      sends: {
        log: {
          input: ({ held }) => ({ taskId: held.taskId }),
          onAccepted: [{ target: "noting", with: { taskId: ({ held }) => held.taskId } }],
        },
      },
    },
    noting: {
      sends: { note: { input: ({ held }) => ({ taskId: held.taskId }), onAccepted: [{ target: "idle" }] } },
    },
  },
});
