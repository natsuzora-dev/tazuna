import { logTask, machine, taskAdded, taskArchived, taskFinished } from "./todo.ts";

export const tracker = machine({
  description: "Record an added task when it is finished, but not when it is put away",
  receives: { taskAdded, taskFinished, taskArchived },
  commands: { logTask },
  initial: "idle",
  states: {
    idle: {},
    tracking: { initial: "open", states: { open: {}, finished: { type: "final" } } },
    logging: {},
  },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "tracking" }] } },
    tracking: { on: { taskArchived: [{ target: "idle" }] }, onDone: [{ target: "logging" }] },
    open: { on: { taskFinished: [{ target: "finished" }] } },
    logging: { sends: { logTask: { onAccepted: [{ target: "idle" }] } } },
  },
});
