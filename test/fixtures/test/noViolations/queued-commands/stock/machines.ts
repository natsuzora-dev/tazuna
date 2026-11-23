import { z } from "zod";
import { count, machine, prepare, started } from "./stock.ts";

export const packer = machine({
  description:
    "On started, send prepare to create items, and send count to count the items when the copies of items have added them to names",
  context: { names: z.array(z.string()).default([]) },
  receives: { started },
  commands: { prepare, count },
  initial: "idle",
  states: {
    idle: {},
    working: {
      type: "parallel",
      states: {
        asking: { initial: "preparing", states: { preparing: {}, counting: {} } },
        copying: {
          initial: "waiting",
          states: {
            waiting: {},
            items: { type: "map", key: { name: z.string() }, initial: "added", states: { added: {} } },
          },
        },
      },
    },
  },
}).chart({
  states: {
    idle: { on: { started: [{ target: "working" }] } },
    preparing: {
      sends: {
        prepare: {
          onAccepted: [{ guard: { copied: ({ context }) => context.names.length > 0 }, target: "counting" }],
          onRejected: [],
        },
      },
    },
    counting: { sends: { count: { onAccepted: [{ target: "idle" }] } } },
    waiting: { always: [{ guard: { itemExists: ({ records }) => records.Item.size > 0 }, target: "items" }] },
    items: { items: ({ records }) => records.Item.map((i) => ({ name: i.id })) },
    added: { entry: { assign: { names: ({ context, key }) => [...context.names, key.name] } } },
  },
});
