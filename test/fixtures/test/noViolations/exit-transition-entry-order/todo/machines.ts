import { z } from "zod";
import { machine, recordSteps, taskAdded, taskCompleted, taskRemoved, taskRenamed } from "./todo.ts";

export const tracer = machine({
  description:
    "Record in steps the order of the writes in the transition from a to b. a has the child a1, and b has the child b1",
  context: { steps: z.array(z.string()).default([]) },
  receives: { taskAdded },
  commands: { recordSteps },
  initial: "a",
  states: {
    a: { initial: "a1", states: { a1: {} } },
    b: { initial: "b1", states: { b1: {} } },
    done: { type: "final" },
  },
}).chart({
  states: {
    a1: { exit: { assign: { steps: ({ context }) => [...context.steps, "a1 exit"] } } },
    b1: {
      entry: { assign: { steps: ({ context }) => [...context.steps, "b1 entry"] } },
      sends: {
        recordSteps: {
          input: ({ context }) => ({ steps: context.steps }),
          onAccepted: [{ target: "done" }],
        },
      },
    },
    a: {
      exit: { assign: { steps: ({ context }) => [...context.steps, "a exit"] } },
      on: { taskAdded: [{ target: "b", assign: { steps: ({ context }) => [...context.steps, "transition assign"] } }] },
    },
    b: { entry: { assign: { steps: ({ context }) => [...context.steps, "b entry"] } } },
  },
});

export const regions = machine({
  description:
    "Record in steps the order of the writes in two transitions selected for one event. The parallel state p has the regions left (child l1) and right (child r1)",
  context: { steps: z.array(z.string()).default([]) },
  receives: { taskCompleted },
  commands: { recordSteps },
  initial: "p",
  states: {
    p: {
      type: "parallel",
      states: { left: { initial: "l1", states: { l1: {} } }, right: { initial: "r1", states: { r1: {} } } },
    },
    q: {},
    done: { type: "final" },
  },
}).chart({
  states: {
    l1: {
      exit: { assign: { steps: ({ context }) => [...context.steps, "l1 exit"] } },
      on: { taskCompleted: [{ assign: { steps: ({ context }) => [...context.steps, "l1 transition assign"] } }] },
    },
    p: {
      exit: { assign: { steps: ({ context }) => [...context.steps, "p exit"] } },
      on: {
        taskCompleted: [{ target: "q", assign: { steps: ({ context }) => [...context.steps, "p transition assign"] } }],
      },
    },
    q: {
      entry: { assign: { steps: ({ context }) => [...context.steps, "q entry"] } },
      sends: {
        recordSteps: {
          input: ({ context }) => ({ steps: context.steps }),
          onAccepted: [{ target: "done" }],
        },
      },
    },
  },
});

export const closer = machine({
  description:
    "Record in steps and seen the order of the writes when a transition of a copy of the map state m and a transition of the owner out of m run in one microstep. The parallel state p has the regions left (the map state m and its child c1, which copies enter) and right (child x)",
  context: { steps: z.array(z.string()).default([]), seen: z.array(z.string()).default([]) },
  receives: { taskRemoved },
  commands: { recordSteps },
  initial: "p",
  states: {
    p: {
      type: "parallel",
      states: {
        left: {
          initial: "m",
          states: { m: { type: "map", key: { name: z.string() }, initial: "c1", states: { c1: {} } } },
        },
        right: { initial: "x", states: { x: {} } },
      },
    },
    q: {},
    done: { type: "final" },
  },
}).chart({
  states: {
    m: {
      items: () => [{ name: "k" }],
      exit: { assign: { steps: ({ context }) => [...context.steps, "m exit"] } },
    },
    c1: {
      exit: { assign: { steps: ({ context }) => [...context.steps, "c1 exit"] } },
      on: {
        taskRemoved: [{ assign: { seen: ({ context }) => [...context.seen, "copy k c1 transition assign"] } }],
      },
    },
    x: {
      exit: { assign: { steps: ({ context }) => [...context.steps, "x exit"] } },
      on: {
        taskRemoved: [{ target: "q", assign: { steps: ({ context }) => [...context.steps, "x transition assign"] } }],
      },
    },
    q: {
      entry: { assign: { steps: ({ context }) => [...context.steps, "q entry"] } },
      sends: {
        recordSteps: {
          input: ({ context }) => ({ steps: [...context.steps, ...context.seen] }),
          onAccepted: [{ target: "done" }],
        },
      },
    },
  },
});

export const opener = machine({
  description: "Record the order in which states are entered",
  context: { steps: z.array(z.string()).default([]) },
  receives: { taskRenamed },
  commands: { recordSteps },
  initial: "idle",
  states: {
    idle: {},
    p: {
      type: "parallel",
      states: { left: { initial: "l1", states: { l1: {}, l2: {} } }, right: { initial: "r1", states: { r1: {} } } },
    },
    done: { type: "final" },
  },
}).chart({
  states: {
    idle: { on: { taskRenamed: [{ target: "l2" }] } },
    p: {
      entry: { assign: { steps: ({ context }) => [...context.steps, "p entry"] } },
      on: { taskRenamed: [{ target: "done" }] },
    },
    l1: { entry: { assign: { steps: ({ context }) => [...context.steps, "l1 entry"] } } },
    l2: {
      entry: { assign: { steps: ({ context }) => [...context.steps, "l2 entry"] } },
      sends: {
        recordSteps: {
          input: ({ context }) => ({ steps: context.steps }),
          onAccepted: [{ target: "done" }],
        },
      },
    },
    r1: { entry: { assign: { steps: ({ context }) => [...context.steps, "r1 entry"] } } },
  },
});
