import { datetime, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), completedAt: datetime.nullable() },
  key: "id",
});

export const { command, machine, event, createEvent, updateEvent, contract, scenario } = service({
  description: "Greet per task and report when a deadline passes",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const taskCompleted = updateEvent({ entity: Task, writes: ["completedAt"] });
export const greeted = event({ payload: { taskId: z.string() } });
export const reminded = event({ payload: { taskId: z.string() } });

export const addTasks = command({
  input: { taskIds: z.array(Task.fields.id) },
  emits: [taskAdded],
}).decide(({ input }) => input.taskIds.map((id) => emit(taskAdded, { id, completedAt: null })));

export const completeTask = command({
  input: { taskId: ref(Task) },
  emits: [taskCompleted],
}).decide(({ input, now }) => [emit(taskCompleted, { id: input.taskId, completedAt: now })]);

export const greet = command({
  input: { taskId: ref(Task) },
  emits: [greeted],
}).decide(({ input }) => [emit(greeted, { taskId: input.taskId })]);

export const remind = command({
  input: { taskId: ref(Task) },
  emits: [reminded],
}).decide(({ input }) => [emit(reminded, { taskId: input.taskId })]);

export const perTask = machine({
  description: "Greet in each copy of an open task, and report when the task is not completed within an hour",
  commands: { greet, remind },
  initial: "rows",
  states: {
    rows: {
      type: "map",
      key: { taskId: ref(Task) },
      initial: "greeting",
      states: { greeting: {}, waiting: { after: ["hour"] }, reminding: {}, done: {} },
    },
  },
}).chart({
  states: {
    rows: {
      // The closure gets the keys in reverse order, which items does not depend on.
      items: ({ records }) => {
        const keys: { taskId: string }[] = [];
        records.Task.filter((t) => t.completedAt === null).map((t) => keys.unshift({ taskId: t.id }));
        return keys;
      },
    },
    greeting: { sends: { greet: { input: ({ key }) => key, onAccepted: [{ target: "waiting" }], onRejected: [] } } },
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "reminding" }] } } },
    reminding: { sends: { remind: { input: ({ key }) => key, onAccepted: [{ target: "done" }], onRejected: [] } } },
  },
});
