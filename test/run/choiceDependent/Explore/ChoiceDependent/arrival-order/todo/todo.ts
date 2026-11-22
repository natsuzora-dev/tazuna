import { emit, entity, instant, ref, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { calendar } from "../calendar/contract.ts";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), due: instant.nullable() },
  key: "id",
});

export const Last = singleEntity({
  description: "The task whose due was set last",
  fields: { taskId: z.string().default("") },
});

export const { command, machine, createEvent, updateEvent, contract, given, scenario } = service({
  name: "todo",
  description: "Keep tasks, each due on the next business day",
  entities: { Task, Last },
});

export const taskAdded = createEvent({ entity: Task });
export const dueSet = updateEvent({ entity: Task, writes: ["due"] });
export const lastSet = updateEvent({ entity: Last, writes: ["taskId"] });

export const addTasks = command({
  input: { taskIds: z.array(Task.fields.id) },
  emits: [taskAdded],
}).decide(({ input }) => input.taskIds.map((id) => emit(taskAdded, { id, due: null })));

export const setDue = command({
  input: { taskId: ref(Task), due: instant },
  emits: [dueSet, lastSet],
}).decide(({ input }) => [emit(dueSet, { id: input.taskId, due: input.due }), emit(lastSet, { taskId: input.taskId })]);

export const dueSetter = machine({
  description:
    "Ask calendar for the next business day in each copy of a task, and set the task's due to it, recording it as the last task set",
  queries: { nextBusinessDay: calendar.nextBusinessDay },
  commands: { setDue },
  initial: "rows",
  states: {
    rows: {
      type: "map",
      key: { taskId: ref(Task) },
      initial: "asking",
      states: { asking: {}, setting: { held: { day: instant } }, done: {} },
    },
  },
}).chart({
  states: {
    rows: { items: ({ records }) => records.Task.filter((t) => t.due === null).map((t) => ({ taskId: t.id })) },
    asking: {
      calls: {
        nextBusinessDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "setting", with: { day: ({ output }) => output.day } }],
        },
      },
    },
    setting: {
      sends: {
        setDue: {
          input: ({ key, held }) => ({ taskId: key.taskId, due: held.day }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const todo = contract({ addTasks });
