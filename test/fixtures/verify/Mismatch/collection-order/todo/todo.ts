import { any, bag, emit, instant, parseInstant, service, set, sortedBy } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, query, screen, event, contract, scenario } = service({
  name: "todo",
  description: "Keep tasks",
});

export const Entry = z.object({ day: z.int(), title: z.string() });

export const tasksListed = event({
  payload: {
    steps: z.array(z.string()),
    titles: bag(z.string()),
    tags: set(z.string()),
    entries: sortedBy(Entry, "day"),
  },
});

export const listTasks = command({ callers: ["client"], emits: [tasksListed] }).decide(() => [
  emit(tasksListed, {
    steps: ["shop", "pay"],
    titles: ["Buy milk", "Buy eggs", "Buy milk"],
    tags: ["home", "store"],
    entries: [
      { day: 2, title: "Buy eggs" },
      { day: 1, title: "Buy milk" },
      { day: 1, title: "Buy bread" },
    ],
  }),
]);

const Slot = z.strictObject({ at: instant, n: z.int() });
const at = (hour: number) => parseInstant("2026-10-25T00:00:00Z") + hour * 3_600_000;

export const taskGroups = query({
  callers: ["client"],
  output: {
    groups: z.array(
      z.strictObject({
        name: z.string(),
        members: bag(z.string()),
        steps: z.array(z.int()),
        slots: sortedBy(Slot, "at"),
      }),
    ),
    either: z.union([bag(z.int()), z.string()]),
    maybe: bag(z.int()).optional(),
    orNull: bag(z.int()).nullable(),
    withDefault: bag(z.int()).default([]),
  },
}).resolve(() => ({
  groups: [
    {
      name: "a",
      members: ["x", "y", "y"],
      steps: [1, 2],
      slots: [
        { at: at(2), n: 1 },
        { at: at(1), n: 2 },
        { at: at(2), n: 3 },
      ],
    },
  ],
  either: [1, 2],
  maybe: [1, 2],
  orNull: [1, 2],
  withDefault: [1, 2],
}));

export const orderedTaskGroups = query({
  callers: ["client"],
  output: {
    groups: z.array(
      z.strictObject({
        name: z.string(),
        members: bag(z.string()),
        steps: z.array(z.int()),
        slots: sortedBy(Slot, "at"),
      }),
    ),
    withDefault: bag(z.int()).default([]),
  },
}).resolve(() => ({
  groups: [
    {
      name: "a",
      members: ["x", "y", "y"],
      steps: [1, 2],
      slots: [
        { at: at(1), n: 1 },
        { at: at(2), n: 2 },
      ],
    },
  ],
  withDefault: [1, 2],
}));

export const tagTask = command({ callers: ["client"], input: { tags: bag(z.string()) }, emits: [] }).decide(() => []);

export const tagScreen = screen({
  description: "A screen that picks a card",
  context: { tags: bag(z.string()).default([]) },
  controls: { pick: { label: "Pick", payload: { tags: bag(z.string()) } } },
  initial: "picking",
  states: { picking: {} },
}).chart({
  offers: { pick: any },
  states: { picking: { on: { pick: [{ assign: { tags: ({ payload }) => payload.tags } }] } } },
});
