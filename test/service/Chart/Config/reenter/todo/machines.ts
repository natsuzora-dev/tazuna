import { machine, remind, taskAdded } from "./todo.ts";

export const keepsDeadline = machine({
  description: "Notify an hour after waiting is entered, without extending the deadline when a task is added",
  receives: { taskAdded },
  commands: { remind },
  initial: "waiting",
  states: { waiting: {}, reminding: {}, done: { type: "final" } },
}).chart({
  states: {
    waiting: {
      on: { taskAdded: [{ target: "waiting", reenter: false }] },
      after: { hour: { delay: { hours: 1 }, onFired: [{ target: "reminding" }] } },
    },
    reminding: {
      sends: { remind: { input: () => ({ by: "keepsDeadline" }), onAccepted: [{ target: "done" }] } },
    },
  },
});

export const restartsDeadline = machine({
  description: "Notify two hours after the last task is added",
  receives: { taskAdded },
  commands: { remind },
  initial: "waiting",
  states: { waiting: {}, reminding: {}, done: { type: "final" } },
}).chart({
  states: {
    waiting: {
      on: { taskAdded: [{ target: "waiting", reenter: true }] },
      after: { twoHours: { delay: { hours: 2 }, onFired: [{ target: "reminding" }] } },
    },
    reminding: {
      sends: {
        remind: { input: () => ({ by: "restartsDeadline" }), onAccepted: [{ target: "done" }] },
      },
    },
  },
});

export const keepsDeadlineToChild = machine({
  description:
    "Notify an hour after waiting is entered, and keep the deadline when a task is added and noted, a child of waiting, is entered",
  receives: { taskAdded },
  commands: { remind },
  initial: "waiting",
  states: { waiting: { initial: "idle", states: { idle: {}, noted: {} } }, reminding: {}, done: { type: "final" } },
}).chart({
  states: {
    waiting: {
      on: { taskAdded: [{ target: "noted", reenter: false }] },
      after: { hour: { delay: { hours: 1 }, onFired: [{ target: "reminding" }] } },
    },
    reminding: {
      sends: {
        remind: { input: () => ({ by: "keepsDeadlineToChild" }), onAccepted: [{ target: "done" }] },
      },
    },
  },
});

export const restartsDeadlineToChild = machine({
  description:
    "Reenter waiting when a task is added, enter noted, a child of waiting, and notify two hours after the last entry",
  receives: { taskAdded },
  commands: { remind },
  initial: "waiting",
  states: {
    waiting: { initial: "idle", states: { idle: {}, noted: {} } },
    reminding: {},
    done: { type: "final" },
  },
}).chart({
  states: {
    waiting: {
      on: { taskAdded: [{ target: "noted", reenter: true }] },
      after: { twoHours: { delay: { hours: 2 }, onFired: [{ target: "reminding" }] } },
    },
    reminding: {
      sends: {
        remind: { input: () => ({ by: "restartsDeadlineToChild" }), onAccepted: [{ target: "done" }] },
      },
    },
  },
});

export const keepsDeadlineInParallel = machine({
  description:
    "Notify an hour after the parallel state waiting is entered, and keep the deadline when a task is added and noted, a child of the region listing of waiting, is entered",
  receives: { taskAdded },
  commands: { remind },
  initial: "waiting",
  states: {
    waiting: {
      type: "parallel",
      states: {
        listing: { initial: "idle", states: { idle: {}, noted: {} } },
        counting: { initial: "counted", states: { counted: {} } },
      },
    },
    reminding: {},
    done: { type: "final" },
  },
}).chart({
  states: {
    waiting: {
      on: { taskAdded: [{ target: "noted", reenter: false }] },
      after: { hour: { delay: { hours: 1 }, onFired: [{ target: "reminding" }] } },
    },
    reminding: {
      sends: {
        remind: { input: () => ({ by: "keepsDeadlineInParallel" }), onAccepted: [{ target: "done" }] },
      },
    },
  },
});
