import { datetime, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { calendar } from "../calendar/contract.ts";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), due: datetime.nullable() },
  key: "id",
});

export const { command, machine, createEvent, updateEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep tasks, each due on the next business day",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const dueSet = updateEvent({ entity: Task, writes: ["due"] });

export const addTasks = command({
  input: { taskIds: z.array(Task.fields.id) },
  emits: [taskAdded],
}).decide(({ input }) => input.taskIds.map((id) => emit(taskAdded, { id, due: null })));

export const setDue = command({
  input: { taskId: ref(Task), due: datetime },
  emits: [dueSet],
}).decide(({ input }) => [emit(dueSet, { id: input.taskId, due: input.due })]);

export const dueSetter = machine({
  description:
    "Ask calendar for the next business day in each copy of a task, with the same input for every task, and set the task's due an hour later",
  queries: { nextBusinessDay: calendar.nextBusinessDay },
  commands: { setDue },
  initial: "rows",
  states: {
    rows: {
      type: "map",
      key: { taskId: ref(Task) },
      context: { day: datetime.nullable().default(null) },
      initial: "asking",
      states: { asking: {}, waiting: {}, setting: { held: { day: datetime } }, done: {} },
    },
  },
}).chart({
  states: {
    rows: { items: ({ records }) => records.Task.filter((t) => t.due === null).map((t) => ({ taskId: t.id })) },
    asking: {
      calls: {
        nextBusinessDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "waiting", assign: { day: ({ output }) => output.day } }],
        },
      },
    },
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "setting" }] } } },
    setting: {
      holds: { day: ({ context }) => context.day },
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
