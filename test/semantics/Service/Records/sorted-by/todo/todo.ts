import { bag, date, datetime, emit, service, set, sortedBy } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, screen } = service({ description: "Keep tasks" });

export const Entry = z.object({ day: z.int(), title: z.string() });

export const tasksListed = event({
  payload: {
    steps: z.array(z.string()),
    titles: bag(z.string()),
    tags: set(z.string()),
    entries: sortedBy(Entry, "day"),
  },
});

export const listTasks = command({ emits: [tasksListed] }).decide(() => [
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

export const tasksPlanned = event({ payload: { entries: sortedBy(Entry, "day") } });

export const planTasks = command({
  input: { entries: sortedBy(Entry, "day") },
  emits: [tasksPlanned],
}).decide(({ input }) => [emit(tasksPlanned, { entries: input.entries })]);

export const Visit = z.object({ at: datetime, on: date, title: z.string() });

export const visitsListed = event({
  payload: { byTime: sortedBy(Visit, "at"), byDay: sortedBy(Visit, "on") },
});

export const listVisits = command({ emits: [visitsListed] }).decide(({ now }) => {
  const visits = [
    { at: now.add({ hours: 2 }), on: Temporal.PlainDate.from("2026-10-25"), title: "Go to the bakery" },
    { at: now, on: Temporal.PlainDate.from("2026-10-27"), title: "Go to the station" },
    { at: now.add({ hours: 1 }), on: Temporal.PlainDate.from("2026-10-26"), title: "Go to the field" },
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
  input: { isFilled: z.boolean() },
  emits: [planChecked],
}).decide(({ input }) => {
  const entries = input.isFilled ? unsorted() : null;
  return [emit(planChecked, { nullable: entries, union: entries })];
});

const isSorted = (entries: readonly { readonly day: number }[]) =>
  entries.every((entry, i) => i === 0 || (entries[i - 1]?.day ?? 0) <= entry.day);

const unsorted = () => [
  { day: 2, title: "Buy eggs" },
  { day: 1, title: "Buy milk" },
];

export const pickScreen = screen({
  description: "A screen that picks a plan",
  output: { entries: sortedBy(Entry, "day") },
  controls: { finish: { label: "Finish" } },
  initial: "picking",
  states: { picking: {}, done: { type: "final" } },
  ensures: { isSortedOutput: ({ output }) => isSorted(output.entries) },
}).chart({ resolve: () => ({ entries: unsorted() }), states: { picking: { on: { finish: [{ target: "done" }] } } } });

export const planScreen = screen({
  description: "A screen that lists plans",
  context: { entries: sortedBy(Entry, "day").default([]) },
  screens: { pick: pickScreen },
  controls: { fill: { label: "Arrange" }, open: { label: "Pick" } },
  initial: "planning",
  states: { planning: {}, picking: {} },
  invariants: { isSortedContext: ({ context }) => isSorted(context.entries) },
}).chart({
  states: {
    planning: { on: { fill: [{ assign: { entries: unsorted } }], open: [{ target: "picking" }] } },
    picking: {
      opens: {
        pick: { modal: true, onDone: [{ target: "planning", assign: { entries: ({ output }) => output.entries } }] },
      },
    },
  },
});
