import { machine, remind, taskAdded } from "./earlyFirstTodo.ts";

export const reminder = machine({
  description: "Remind of an added task once, by the first of two deadlines, earlyDeadline declared first",
  receives: { taskAdded },
  commands: { remind },
  initial: "idle",
  states: { idle: {}, waiting: {}, early: {}, late: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "waiting" }] } },
    waiting: {
      after: {
        earlyDeadline: { delay: { hours: 1 }, onFired: [{ target: "early" }] },
        lateDeadline: { delay: { hours: 1 }, onFired: [{ target: "late" }] },
      },
    },
    early: { sends: { remind: { input: () => ({ by: "early" }), onAccepted: [{ target: "done" }] } } },
    late: { sends: { remind: { input: () => ({ by: "late" }), onAccepted: [{ target: "done" }] } } },
  },
});
