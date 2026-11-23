import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { machine, given, scenario } = service({ name: "planner", description: "Plan the tasks" });

export const adder = machine({
  description: "Add a task when the service starts",
  commands: { addTask: todo.addTask },
  initial: "adding",
  states: { adding: {}, done: { type: "final" } },
}).chart({
  states: {
    adding: {
      sends: {
        addTask: {
          input: () => ({ taskId: "task-1", title: "Buy milk" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});
