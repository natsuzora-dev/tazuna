import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, scenario } = service({ description: "Mark per task" });

export const taskStarred = event({ payload: { taskId: z.string() } });
export const noted = event({ payload: { taskId: z.string() } });

export const starTask = command({
  input: { taskId: z.string() },
  emits: [taskStarred],
}).decide(({ input }) => [emit(taskStarred, { taskId: input.taskId })]);

export const note = command({
  input: { taskId: z.string() },
  emits: [noted],
}).decide(({ input }) => [emit(noted, { taskId: input.taskId })]);

export const perTask = machine({
  description: "Mark only in the copies of tasks whose taskId fits the key schema",
  receives: { taskStarred },
  commands: { note },
  initial: "rows",
  states: {
    rows: {
      type: "map",
      key: { taskId: z.string().startsWith("task-") },
      initial: "idle",
      states: { idle: {}, noting: {} },
    },
  },
}).chart({
  states: {
    rows: { items: () => [{ taskId: "task-1" }] },
    idle: { on: { taskStarred: [{ target: "noting" }] } },
    noting: {
      sends: { note: { input: ({ key }) => key, onAccepted: [{ target: "idle" }] } },
    },
  },
});
