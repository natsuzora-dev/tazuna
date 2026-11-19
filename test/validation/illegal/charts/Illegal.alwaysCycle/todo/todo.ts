import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, machine, createEvent, contract } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

// A cycle of guarded transitions only is not reported, because the guards can stop it.
export const guardedFlow = machine({
  description: "Alternate between two states",
  receives: { taskAdded },
  initial: "a",
  states: {
    a: {},
    b: {},
  },
}).chart({
  states: {
    a: { always: [{ guard: { hasTask: ({ records }) => records.Task.size > 0 }, target: "b" }] },
    b: { always: [{ guard: { noTask: ({ records }) => records.Task.size === 0 }, target: "a" }] },
  },
});

export const mixedLeavingOnEvent = machine({
  description: "Leave c only while there are tasks, and return on taskAdded",
  receives: { taskAdded },
  initial: "c",
  states: { c: {}, d: {} },
}).chart({
  states: {
    c: { always: [{ guard: { hasTask: ({ records }) => records.Task.size > 0 }, target: "d" }] },
    d: { on: { taskAdded: [{ target: "c" }] } },
  },
});

export const flow = machine({
  description: "Alternate between two states",
  receives: { taskAdded },
  initial: "a",
  states: { a: {}, b: {} },
}).chart({ states: { a: { always: [{ target: "b" }] }, b: { always: [{ target: "a" }] } } });

export const mixed = machine({
  description: "Leave a only while there are tasks",
  receives: { taskAdded },
  initial: "c",
  states: { c: {}, d: {} },
}).chart({
  states: {
    c: { always: [{ guard: { hasTask: ({ records }) => records.Task.size > 0 }, target: "d" }] },
    d: { always: [{ target: "c" }] },
  },
});

// Entering p also enters its initial state p1, whose always transition leaves again.
export const nested = machine({
  description: "Return to the initial state of p",
  receives: { taskAdded },
  initial: "p",
  states: { p: { initial: "p1", states: { p1: {} } }, q: {} },
}).chart({ states: { p1: { always: [{ target: "q" }] }, q: { always: [{ target: "p" }] } } });

// The always transition of r to its child r2 with reenter: false does not exit r, so it is selected again.
export const inward = machine({
  description: "Enter a child of r",
  receives: { taskAdded },
  initial: "r",
  states: { r: { initial: "r1", states: { r1: {}, r2: {} } }, s: {} },
}).chart({
  states: {
    r: { on: { taskAdded: [{ target: "s" }] }, always: [{ target: "r2", reenter: false }] },
    s: { always: [{ target: "r" }] },
  },
});

// A transition without a target stays in its state.
export const counting = machine({
  description: "Count without end",
  context: { count: z.number().int().default(0) },
  receives: { taskAdded },
  initial: "t",
  states: { t: {} },
}).chart({ states: { t: { always: [{ assign: { count: ({ context }) => context.count + 1 } }] } } });

export const todo = contract({ addTask });
