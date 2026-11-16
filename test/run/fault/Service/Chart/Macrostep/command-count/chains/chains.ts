import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, scenario } = service({ description: "Ping in chains" });

export const ping = command({ emits: [] }).decide(() => []);

export const pinger = machine({
  description: "Run 101 chains of 100 pings at the start, each ping sent when the one before is accepted",
  commands: { ping },
  initial: "chains",
  states: {
    chains: {
      type: "map",
      key: { chain: z.number() },
      context: { pings: z.number().default(1) },
      initial: "pinging",
      states: { pinging: {} },
    },
  },
}).chart({
  states: {
    chains: { items: () => Array.from({ length: 101 }, (_, chain) => ({ chain })) },
    pinging: {
      sends: {
        ping: {
          onAccepted: [
            {
              guard: { hasMore: ({ context }) => context.pings < 100 },
              target: "pinging",
              reenter: true,
              assign: { pings: ({ context }) => context.pings + 1 },
            },
          ],
        },
      },
    },
  },
});
