import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({ description: "Ping when a task is added" });

export const taskAdded = event({ payload: { id: z.string() } });
export const pinged = event({});

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const ping = command({ emits: [pinged] }).decide(() => [emit(pinged, {})]);

export const pinger = machine({
  description: "Ping when a task is added; sending lists pinged with no transitions",
  receives: { taskAdded, pinged },
  commands: { ping },
  initial: "idle",
  states: { idle: {}, sending: {}, done: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "sending" }] } },
    sending: {
      on: { pinged: [] },
      sends: { ping: { onAccepted: [{ target: "done" }] } },
    },
  },
});

export const pingers = contract({ addTask });
