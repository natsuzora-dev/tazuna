import { z } from "zod";
import { labelsOpened, machine, notify, remindPressed, Task, taskSelected } from "./todo.ts";

export const watcher = machine({
  description: "Notify the title of the selected task, and notify it again on remind when the task was renamed since",
  receives: { taskSelected, remindPressed },
  commands: { notify },
  initial: "idle",
  states: { idle: {}, watching: { held: { taskId: z.string(), title: Task.fields.title } } },
}).chart({
  states: {
    idle: {
      on: {
        taskSelected: [
          {
            target: "watching",
            with: {
              taskId: ({ payload }) => payload.taskId,
              title: ({ payload, records }) => records.Task.get(payload.taskId)?.title,
            },
          },
        ],
      },
    },
    watching: {
      on: {
        remindPressed: [
          {
            guard: { renamed: ({ held, records }) => records.Task.get(held.taskId)?.title !== held.title },
            target: "watching",
            reenter: true,
            with: {
              taskId: ({ held }) => held.taskId,
              title: ({ held, records }) => records.Task.get(held.taskId)?.title,
            },
          },
        ],
      },
      sends: { notify: { input: ({ held }) => ({ text: held.title }), onAccepted: [] } },
    },
  },
});

export const labels = machine({
  description: "Notify the left and right labels when the labels are opened",
  context: { last: z.string().default("") },
  receives: { labelsOpened },
  commands: { notify },
  initial: "idle",
  states: {
    idle: {},
    open: {
      type: "parallel",
      states: {
        left: {
          initial: "leftShowing",
          states: { leftShowing: { held: { label: z.string() } }, leftClosed: {} },
        },
        right: { initial: "rightShowing", states: { rightShowing: { held: { label: z.string() } } } },
      },
    },
  },
}).chart({
  states: {
    idle: { on: { labelsOpened: [{ target: "open" }] } },
    open: { on: { labelsOpened: [{ target: "idle" }] } },
    left: { initial: { with: { label: () => "left" } } },
    right: { initial: { with: { label: () => "right" } } },
    leftShowing: {
      sends: {
        notify: {
          input: ({ held }) => ({ text: held.label }),
          onAccepted: [{ target: "leftClosed", assign: { last: ({ held }) => held.label } }],
        },
      },
    },
    leftClosed: {
      sends: { notify: { input: ({ context }) => ({ text: context.last }), onAccepted: [] } },
    },
    rightShowing: {
      sends: { notify: { input: ({ held }) => ({ text: held.label }), onAccepted: [] } },
    },
  },
});
