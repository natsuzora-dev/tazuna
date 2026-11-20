import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task of the user", fields: { id: z.string() }, key: "id" });

export const { command, machine, createEvent, event, contract, given, scenario } = service({
  name: "greeter",
  description: "Greet per task in the order of the copy keys",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const greeted = event({ payload: { taskId: z.string(), rank: z.int() } });

export const addTasks = command({
  input: { taskIds: z.array(Task.fields.id) },
  emits: [taskAdded],
}).decide(({ input }) => input.taskIds.map((id) => emit(taskAdded, { id })));

export const greet = command({
  input: { taskId: ref(Task), rank: z.int() },
  emits: [greeted],
}).decide(({ input }) => [emit(greeted, input)]);

const ranks: Readonly<Record<string, { readonly rank: number }>> = { "task-1": { rank: 1 } };

export const perTask = machine({
  description: "Greet in each copy of a task; a copy key leaves its rank to the default unless the task is task-1",
  commands: { greet },
  initial: "rows",
  states: {
    rows: {
      type: "map",
      key: { taskId: ref(Task), rank: z.int().default(0) },
      initial: "greeting",
      states: { greeting: {}, done: {} },
    },
  },
}).chart({
  states: {
    rows: {
      // The types ask for rank, but a key that leaves it out at run time gets its default from the parse.
      items: ({ records }) => records.Task.map((t) => Object.assign({ taskId: t.id }, ranks[t.id])),
    },
    greeting: { sends: { greet: { input: ({ key }) => key, onAccepted: [{ target: "done" }], onRejected: [] } } },
  },
});
