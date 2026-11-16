import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract } = service({ description: "Watch the added tasks" });

export const taskAdded = event({ payload: { title: z.string() } });

export const addTask = command({ input: { title: z.string() }, emits: [taskAdded] }).decide(({ input }) => [
  emit(taskAdded, { title: input.title }),
]);

export const watcher = machine({
  description: "Stop at the first titled task",
  receives: { taskAdded },
  initial: "watching",
  states: { watching: {}, done: { type: "final" } },
}).chart({
  states: {
    watching: {
      on: {
        taskAdded: [
          {
            guard: {
              titled: ({ payload }) => {
                if (payload.title === "") throw new Error("the task has no title");
                return true;
              },
            },
            target: "done",
          },
        ],
      },
    },
  },
});

export const todo = contract({ addTask });
