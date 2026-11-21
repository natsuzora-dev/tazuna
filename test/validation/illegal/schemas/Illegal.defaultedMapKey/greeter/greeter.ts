import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task of the user", fields: { id: z.string() }, key: "id" });

export const { command, machine, event } = service({
  name: "greeter",
  description: "Greet per task",
  entities: { Task },
});

export const greeted = event({ payload: { taskId: z.string(), rank: z.int() } });

export const greet = command({
  input: { taskId: ref(Task), rank: z.int(), label: z.object({ text: z.string() }) },
  emits: [greeted],
}).decide(({ input }) => [emit(greeted, { taskId: input.taskId, rank: input.rank })]);

export const perTask = machine({
  description: "Greet in each copy of a task",
  commands: { greet },
  initial: "rows",
  states: {
    rows: {
      type: "map",
      key: { taskId: ref(Task), rank: z.int().default(0), label: z.object({ text: z.string().default("") }) },
      initial: "greeting",
      states: { greeting: {}, done: {} },
    },
  },
}).chart({
  states: {
    rows: { items: ({ records }) => records.Task.map((t) => ({ taskId: t.id, rank: 1, label: { text: t.id } })) },
    greeting: { sends: { greet: { input: ({ key }) => key, onAccepted: [{ target: "done" }], onRejected: [] } } },
  },
});
