import { machine, remind, taskAdded } from "./todo.ts";

export const earlyReminder = machine({
  description: "Remind of an added task an hour later",
  receives: { taskAdded },
  commands: { remind },
  initial: "idle",
  states: { idle: {}, waiting: {}, reminding: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "waiting" }] } },
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "reminding" }] } } },
    reminding: {
      sends: { remind: { input: () => ({ by: "early" }), onAccepted: [{ target: "done" }] } },
    },
  },
});

export const lateReminder = machine({
  description: "Remind of an added task an hour later, from another reminder",
  receives: { taskAdded },
  commands: { remind },
  initial: "idle",
  states: { idle: {}, waiting: {}, reminding: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "waiting" }] } },
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "reminding" }] } } },
    reminding: {
      sends: { remind: { input: () => ({ by: "late" }), onAccepted: [{ target: "done" }] } },
    },
  },
});
