import { z } from "zod";
import { labelsOpened, machine, notify, remindPressed, Task, taskSelected } from "./todo.ts";

export const watcher = machine({
  description: "Notify the current title of the selected task each time remind is pressed",
  context: { taskId: z.string().nullable().default(null) },
  receives: { taskSelected, remindPressed },
  commands: { notify },
  initial: "idle",
  states: { idle: {}, watching: { held: { title: Task.fields.title } } },
}).chart({
  states: {
    idle: { on: { taskSelected: [{ target: "watching", assign: { taskId: ({ payload }) => payload.taskId } }] } },
    watching: {
      holds: {
        title: ({ context, records }) => (context.taskId === null ? null : records.Task.get(context.taskId)?.title),
      },
      on: { remindPressed: [{ target: "watching", reenter: true }] },
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
    leftShowing: {
      holds: { label: () => "left" },
      sends: {
        notify: {
          input: ({ held }) => ({ text: held.label }),
          onAccepted: [{ target: "leftClosed", assign: { last: ({ held }) => `Closed ${held.label}` } }],
        },
      },
    },
    leftClosed: {
      sends: { notify: { input: ({ context }) => ({ text: context.last }), onAccepted: [] } },
    },
    rightShowing: {
      holds: { label: () => "right" },
      sends: { notify: { input: ({ held }) => ({ text: held.label }), onAccepted: [] } },
    },
  },
});
