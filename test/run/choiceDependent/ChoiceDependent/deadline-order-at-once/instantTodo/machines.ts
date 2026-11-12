import { machine, remind, taskAdded } from "./instantTodo.ts";

export const reminder = machine({
  description: "Remind of an added task once, by the first of two deadlines that come at once",
  receives: { taskAdded },
  commands: { remind },
  initial: "idle",
  states: { idle: {}, waiting: {}, early: {}, late: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "waiting" }] } },
    waiting: {
      after: {
        lateDeadline: { delay: { seconds: 0 }, onFired: [{ target: "late" }] },
        earlyDeadline: { delay: { seconds: 0 }, onFired: [{ target: "early" }] },
      },
    },
    early: { sends: { remind: { input: () => ({ by: "early" }), onAccepted: [{ target: "done" }] } } },
    late: { sends: { remind: { input: () => ({ by: "late" }), onAccepted: [{ target: "done" }] } } },
  },
});
