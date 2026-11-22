import { any, bag, date, emit, instant, type Runs, service, set, sortedBy } from "@natsuzora-dev/tazuna";
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

const cents = z.codec(z.string(), z.int(), {
  decode: (text) => Math.round(Number(text) * 100),
  encode: (n) => (n / 100).toFixed(2),
});

export const pricesListed = event({ payload: { prices: bag(cents) } });

export const listPrices = command({ emits: [pricesListed] }).decide(() => [emit(pricesListed, { prices: [150, 20] })]);

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

export const listGroups = command({ emits: [groupsListed] }).decide(() => [
  emit(groupsListed, {
    tagged: { counts: [3, 1] },
    extended: { name: "Shop", counts: [3, 1] },
    named: { kind: "counted", name: "Shop", counts: [3, 1] },
  }),
]);

type Chain = { readonly name: string; readonly next: Chain | null };
const Chain: z.ZodType<Chain> = z.lazy(() => z.object({ name: z.string(), next: Chain.nullable() }));

export const linked = event({ payload: { link: z.union([Chain, z.object({ tags: bag(z.string()) })]) } });

export const link = command({ emits: [linked] }).decide(() => [emit(linked, { link: { tags: ["shop", "home"] } })]);

export const shelved = event({ payload: { names: bag(z.string()), entries: sortedBy(Entry, "day") } });

export const shelve = command({
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
  input: { entries: sortedBy(Entry, "day") },
  emits: [tasksPlanned],
}).decide(({ input }) => [emit(tasksPlanned, { entries: input.entries })]);

export const Visit = z.object({ at: instant, on: date, title: z.string() });

export const visitsListed = event({
  payload: { byTime: sortedBy(Visit, "at"), byDay: sortedBy(Visit, "on") },
});

export const listVisits = command({ emits: [visitsListed] }).decide(({ now }) => {
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
  input: { isFilled: z.boolean() },
  emits: [planChecked],
}).decide(({ input }) => {
  const entries = input.isFilled ? unsorted() : null;
  return [emit(planChecked, { nullable: entries, union: entries })];
});

const isSorted = (runs: Runs<{ readonly day: number }>) =>
  runs.every((run, i) => i === 0 || (runs[i - 1]?.max((e) => e.day) ?? 0) < (run.min((e) => e.day) ?? 0));

const unsorted = () => [
  { day: 2, title: "Buy eggs" },
  { day: 1, title: "Buy milk" },
];

export const plan = query({
  output: { titles: bag(z.string()), entries: sortedBy(Entry, "day") },
}).resolve(() => ({ titles: ["Buy milk", "Buy eggs"], entries: unsorted() }));

export const pickScreen = screen({
  description: "A screen that picks a plan",
  output: { entries: sortedBy(Entry, "day") },
  controls: { finish: { label: "Finish" } },
  initial: "picking",
  states: { picking: {}, done: { type: "final" } },
  ensures: { isSortedOutput: ({ output }) => isSorted(output.entries) },
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
  invariants: { isSortedContext: ({ context }) => isSorted(context.entries) },
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
