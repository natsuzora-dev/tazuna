import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({ description: "Notify per task" });

export const taskStarred = event({ payload: { taskId: z.string() } });
export const allCleared = event({});
export const notified = event({ payload: { taskId: z.string() } });

export const starTask = command({
  input: { taskId: z.string() },
  emits: [taskStarred],
}).decide(({ input }) => [emit(taskStarred, { taskId: input.taskId })]);

export const clearAll = command({
  emits: [allCleared],
}).decide(() => [emit(allCleared, {})]);

export const notify = command({
  input: { taskId: z.string() },
  emits: [notified],
}).decide(({ input }) => [emit(notified, { taskId: input.taskId })]);

export const perTask = machine({
  description: "Notify in each task copy",
  receives: { taskStarred, allCleared },
  commands: { notify },
  initial: "rows",
  states: { rows: { type: "map", key: { taskId: z.string() }, initial: "idle", states: { idle: {}, notifying: {} } } },
}).chart({
  states: {
    rows: { items: () => [{ taskId: "task-1" }, { taskId: "task-2" }] },
    idle: { on: { taskStarred: [{ target: "notifying" }], allCleared: [{ target: "notifying" }] } },
    notifying: {
      sends: {
        notify: { input: ({ key }) => key, onAccepted: [{ target: "idle" }] },
      },
    },
  },
});
