import { contract, emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event } = service({ description: "Ping in a chain for each added task" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const pinged = event({});

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const ping = command({ emits: [pinged] }).decide(() => [emit(pinged, {})]);

export const echo = machine({
  description:
    "Ping 100 times in a chain for each added task, each ping sent when echo receives the pinged event of the one before",
  context: { pings: z.number().default(0) },
  receives: { taskAdded, pinged },
  commands: { ping },
  initial: "idle",
  states: { idle: {}, pinging: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "pinging", assign: { pings: () => 1 } }] } },
    pinging: {
      on: {
        pinged: [
          {
            guard: { hasMore: ({ context }) => context.pings < 100 },
            target: "pinging",
            reenter: true,
            assign: { pings: ({ context }) => context.pings + 1 },
          },
          { target: "idle" },
        ],
      },
      sends: { ping: { onAccepted: [] } },
    },
  },
});

export const echoes = contract({ addTask });
