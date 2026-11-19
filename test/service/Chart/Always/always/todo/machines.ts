import { z } from "zod";
import { condition, count, list, machine, markRow, rowsOpened, signalled, taskAdded, warn } from "./todo.ts";

export const workload = machine({
  description: "Warn when there are more than two tasks, and stop warning when there are two or fewer again",
  commands: { warn },
  initial: "quiet",
  states: { quiet: {}, warning: {} },
}).chart({
  states: {
    quiet: { always: [{ guard: { tooMany: ({ records }) => records.Task.size > 2 }, target: "warning" }] },
    warning: {
      always: [{ guard: { fewEnough: ({ records }) => records.Task.size <= 2 }, target: "quiet" }],
      sends: { warn: { onAccepted: [] } },
    },
  },
});

const fourOrMore = condition(({ records }) => records.Task.size >= 4);
const fewerThanFour = condition(({ records }) => records.Task.size < 4);

export const review = machine({
  description:
    "When there are four or more tasks, count the tasks and list them once each in two regions, and wait again when there are fewer than four",
  commands: { count, list },
  initial: "reviewing",
  states: {
    reviewing: {
      type: "parallel",
      states: {
        counting: { initial: "countWaiting", states: { countWaiting: {}, countDone: {} } },
        listing: { initial: "listWaiting", states: { listWaiting: {}, listDone: {} } },
      },
    },
  },
}).chart({
  states: {
    countWaiting: { always: [{ guard: { fourOrMore }, target: "countDone" }] },
    countDone: {
      always: [{ guard: { fewerThanFour }, target: "countWaiting" }],
      sends: { count: { onAccepted: [] } },
    },
    listWaiting: { always: [{ guard: { fourOrMore }, target: "listDone" }] },
    listDone: {
      always: [{ guard: { fewerThanFour }, target: "listWaiting" }],
      sends: { list: { onAccepted: [] } },
    },
  },
});

export const chain = machine({
  description:
    "When the task chain is added, add the key to names of the owner when a copy of the map state writer in the region right enters, start a copy of the map state reader in the region left for each key in names, and send count from that copy",
  context: { names: z.array(z.string()).default([]) },
  receives: { taskAdded },
  commands: { count },
  initial: "idle",
  states: {
    idle: {},
    p: {
      type: "parallel",
      states: {
        left: {
          initial: "reader",
          states: { reader: { type: "map", key: { name: z.string() }, initial: "r1", states: { r1: {} } } },
        },
        right: {
          initial: "writer",
          states: { writer: { type: "map", key: { name: z.string() }, initial: "w1", states: { w1: {} } } },
        },
      },
    },
  },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ guard: { chainTask: ({ payload }) => payload.id === "chain" }, target: "p" }] } },
    reader: { items: ({ context }) => context.names.map((name) => ({ name })) },
    r1: { sends: { count: { onAccepted: [] } } },
    writer: { items: () => [{ name: "a" }] },
    w1: { entry: { assign: { names: ({ context, key }) => [...context.names, key.name] } } },
  },
});

export const gate = machine({
  description:
    "Enter ready when a signal is recorded, enter opened and count the tasks when the signal arrives in ready, and go back to idle",
  receives: { signalled },
  commands: { count },
  initial: "idle",
  states: { idle: {}, ready: {}, opened: {} },
}).chart({
  states: {
    idle: { always: [{ guard: { signalRecorded: ({ records }) => records.Signal.size > 0 }, target: "ready" }] },
    ready: { on: { signalled: [{ target: "opened" }] } },
    opened: { sends: { count: { onAccepted: [{ target: "idle" }] } } },
  },
});

export const rows = machine({
  description: "Mark row a and then row b when the rows are opened",
  context: { isOpen: z.boolean().default(false), done: z.array(z.string()).default([]) },
  receives: { rowsOpened },
  commands: { markRow },
  initial: "rows",
  states: {
    rows: {
      type: "map",
      key: { name: z.string() },
      initial: "closed",
      states: { closed: {}, marking: {}, marked: {} },
    },
  },
}).chart({
  on: { rowsOpened: [{ assign: { isOpen: () => true } }] },
  states: {
    rows: { items: () => [{ name: "a" }, { name: "b" }] },
    closed: {
      always: [
        {
          guard: { isTurn: ({ context, key }) => (key.name === "a" ? context.isOpen : context.done.includes("a")) },
          target: "marking",
        },
      ],
    },
    marking: {
      sends: {
        markRow: {
          input: ({ key }) => key,
          onAccepted: [{ target: "marked", assign: { done: ({ context, key }) => [...context.done, key.name] } }],
        },
      },
    },
  },
});
