import { any, bag, date, emit, instant, service, set, sortedBy } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, query, screen, contract, given, scenario } = service({
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

export const groupsListed = event({
  payload: {
    tagged: z.union([z.object({ note: z.string().optional() }), z.object({ counts: bag(z.int()) })]),
    extended: z.union([z.object({ name: z.string() }), z.object({ name: z.string(), counts: bag(z.int()) })]),
    named: z.discriminatedUnion("kind", [
      z.object({ kind: z.enum(["plain", "empty"]), name: z.string() }),
      z.object({ kind: z.literal("counted"), name: z.string(), counts: bag(z.int()) }),
    ]),
  },
});

export const listGroups = command({ callers: ["client"], emits: [groupsListed] }).decide(() => [
  emit(groupsListed, {
    tagged: { counts: [3, 1] },
    extended: { name: "Shop", counts: [3, 1] },
    named: { kind: "counted", name: "Shop", counts: [3, 1] },
  }),
]);

export const shelved = event({ payload: { names: bag(z.string()), entries: sortedBy(Entry, "day") } });

export const shelve = command({
  callers: ["client"],
  input: {
    names: bag(z.string()).default(["shop", "home"]),
    entries: sortedBy(Entry, "day").default([
      { day: 2, title: "Buy eggs" },
      { day: 1, title: "Buy milk" },
    ]),
  },
  emits: [shelved],
}).decide(({ input }) => [emit(shelved, { names: input.names, entries: input.entries })]);

export const tasksPlanned = event({ payload: { entries: sortedBy(Entry, "day") } });

export const planTasks = command({
  callers: ["client"],
  input: { entries: sortedBy(Entry, "day") },
  emits: [tasksPlanned],
}).decide(({ input }) => [emit(tasksPlanned, { entries: input.entries })]);

export const Visit = z.object({ at: instant, on: date, title: z.string() });

export const visitsListed = event({
  payload: { byTime: sortedBy(Visit, "at"), byDay: sortedBy(Visit, "on") },
});

export const listVisits = command({ callers: ["client"], emits: [visitsListed] }).decide(({ now }) => {
  const visits = [
    { at: now + 2 * 3_600_000, on: "2026-10-25", title: "Go to the bakery" },
    { at: now, on: "2026-10-27", title: "Go to the station" },
    { at: now + 3_600_000, on: "2026-10-26", title: "Go to the field" },
  ];
  return [emit(visitsListed, { byTime: visits, byDay: visits })];
});

export const planChecked = event({
  payload: {
    nullable: sortedBy(Entry, "day").nullable(),
    union: z.union([sortedBy(Entry, "day"), z.null()]),
  },
});

export const checkPlan = command({
  callers: ["client"],
  input: { isFilled: z.boolean() },
  emits: [planChecked],
}).decide(({ input }) => {
  const entries = input.isFilled ? unsorted() : null;
  return [emit(planChecked, { nullable: entries, union: entries })];
});

const unsorted = () => [
  { day: 2, title: "Buy eggs" },
  { day: 1, title: "Buy milk" },
];

export const plan = query({
  callers: ["client"],
  output: { titles: bag(z.string()), entries: sortedBy(Entry, "day") },
}).resolve(() => ({ titles: ["Buy milk", "Buy eggs"], entries: unsorted() }));

export const pickScreen = screen({
  description: "A screen that picks a plan",
  output: { entries: sortedBy(Entry, "day") },
  controls: { finish: { label: "Finish" } },
  initial: "picking",
  states: { picking: {}, done: { type: "final" } },
}).chart({
  offers: { finish: any },
  resolve: () => ({ entries: unsorted() }),
  states: { picking: { on: { finish: [{ target: "done" }] } } },
});

export const planScreen = screen({
  description: "A screen that lists plans",
  context: { entries: sortedBy(Entry, "day").default([]) },
  screens: { pick: pickScreen },
  controls: { fill: { label: "Arrange" }, open: { label: "Pick" } },
  initial: "planning",
  states: { planning: {}, picking: {} },
}).chart({
  offers: { fill: any, open: any },
  states: {
    planning: { on: { fill: [{ assign: { entries: unsorted } }], open: [{ target: "picking" }] } },
    picking: {
      opens: {
        pick: { modal: true, onDone: [{ target: "planning", assign: { entries: ({ output }) => output.entries } }] },
      },
    },
  },
});
