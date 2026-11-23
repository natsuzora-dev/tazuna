import { z } from "zod";
import { machine, remind, taskAdded, taskPicked } from "./todo.ts";

export const reminder = machine({
  description:
    "Notify through a transition of the region left, the region right, or running, depending on the id of the added task",
  receives: { taskAdded },
  commands: { remind },
  initial: "running",
  states: {
    running: {
      type: "parallel",
      states: {
        left: { initial: "leftWaiting", states: { leftWaiting: {}, leftNotifying: {}, leftDone: { type: "final" } } },
        right: {
          initial: "rightWaiting",
          states: { rightWaiting: {}, rightNotifying: {}, rightDone: { type: "final" } },
        },
      },
    },
    stopping: {},
    stopped: { type: "final" },
  },
}).chart({
  states: {
    running: { on: { taskAdded: [{ target: "stopping" }] } },
    leftWaiting: {
      on: { taskAdded: [{ guard: { isLeft: ({ payload }) => payload.taskId === "left" }, target: "leftNotifying" }] },
    },
    leftNotifying: {
      sends: { remind: { input: () => ({ by: "left" }), onAccepted: [{ target: "leftDone" }] } },
    },
    rightWaiting: {
      on: {
        taskAdded: [{ guard: { isRight: ({ payload }) => payload.taskId === "right" }, target: "rightNotifying" }],
      },
    },
    rightNotifying: {
      sends: { remind: { input: () => ({ by: "right" }), onAccepted: [{ target: "rightDone" }] } },
    },
    stopping: {
      sends: { remind: { input: () => ({ by: "running" }), onAccepted: [{ target: "stopped" }] } },
    },
  },
});

export const picker = machine({
  description: "Notify about the picked task",
  receives: { taskPicked },
  commands: { remind },
  initial: "rows",
  states: {
    rows: {
      type: "map",
      key: { name: z.string() },
      initial: "rowWaiting",
      states: { rowWaiting: {}, rowNotifying: {}, rowDone: {} },
    },
    rowsStopping: {},
    rowsStopped: { type: "final" },
  },
}).chart({
  states: {
    rows: { items: () => [{ name: "task-1" }, { name: "task-2" }], on: { taskPicked: [{ target: "rowsStopping" }] } },
    rowWaiting: {
      on: {
        taskPicked: [
          { guard: { isOwnTask: ({ payload, key }) => payload.taskId === key.name }, target: "rowNotifying" },
        ],
      },
    },
    rowNotifying: {
      sends: {
        remind: { input: ({ key }) => ({ by: key.name }), onAccepted: [{ target: "rowDone" }] },
      },
    },
    rowsStopping: {
      sends: { remind: { input: () => ({ by: "rows" }), onAccepted: [{ target: "rowsStopped" }] } },
    },
  },
});
