import { addDays, date, emit, service } from "@natsuzora-dev/tazuna";

export const { command, machine, event, contract, scenario } = service({
  name: "todo",
  description: "Watch the added tasks",
});

export const taskAdded = event({ payload: { due: date } });

export const addTask = command({ input: { due: date }, emits: [taskAdded] }).decide(({ input }) => [
  emit(taskAdded, { due: input.due }),
]);

export const watcher = machine({
  description: "Stop at the first task due before year 10000",
  receives: { taskAdded },
  initial: "watching",
  states: { watching: {}, done: { type: "final" } },
}).chart({
  states: {
    watching: {
      on: {
        taskAdded: [
          {
            guard: { dueBeforeYearTenThousand: ({ payload }) => addDays(payload.due, 3_000_000) > payload.due },
            target: "done",
          },
        ],
      },
    },
  },
});

export const todo = contract({ addTask });
