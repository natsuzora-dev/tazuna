import { machine, remind, taskAdded } from "./todo.ts";

export const reminder = machine({
  description: "Report an hour after a task is added",
  receives: { taskAdded },
  commands: { remind },
  initial: "idle",
  states: { idle: {}, waiting: {}, reminding: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "waiting" }] } },
    waiting: { after: { hour: { delay: 3_600_000, onFired: [{ target: "reminding" }] } } },
    reminding: { sends: { remind: { onAccepted: [] } } },
  },
});
