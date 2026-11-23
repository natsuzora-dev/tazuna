import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { calendar } from "../calendar/contract.ts";

export const Task = entity({
  description: "A task of the user",
  fields: { id: z.string(), day: z.string(), booked: z.boolean().nullable() },
  key: "id",
});

export const { command, machine, createEvent, updateEvent, contract, given, scenario } = service({
  name: "todo",
  description: "Keep tasks, each booking its day on the calendar",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const bookedSet = updateEvent({ entity: Task, writes: ["booked"] });

export const addTasks = command({
  callers: ["client"],
  input: { tasks: z.array(z.object({ id: Task.fields.id, day: z.string() })) },
  emits: [taskAdded],
}).decide(({ input }) => input.tasks.map((t) => emit(taskAdded, { id: t.id, day: t.day, booked: null })));

export const setBooked = command({
  callers: ["client", "todo"],
  input: { taskId: ref(Task), booked: z.boolean() },
  emits: [bookedSet],
}).decide(({ input }) => [emit(bookedSet, { id: input.taskId, booked: input.booked })]);

export const booker = machine({
  description: "Reserve the day of each task on the calendar, and record whether the calendar booked it",
  commands: { reserve: calendar.reserve, setBooked },
  initial: "rows",
  states: {
    rows: {
      type: "map",
      key: { taskId: ref(Task), day: z.string() },
      initial: "reserving",
      states: { reserving: {}, booked: {}, refused: {}, done: {} },
    },
  },
}).chart({
  states: {
    rows: {
      items: ({ records }) => records.Task.filter((t) => t.booked === null).map((t) => ({ taskId: t.id, day: t.day })),
    },
    reserving: {
      sends: {
        reserve: {
          input: ({ key }) => ({ day: key.day }),
          onAccepted: [{ target: "booked" }],
          onRejected: [{ target: "refused" }],
        },
      },
    },
    booked: {
      sends: {
        setBooked: {
          input: ({ key }) => ({ taskId: key.taskId, booked: true }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
    refused: {
      sends: {
        setBooked: {
          input: ({ key }) => ({ taskId: key.taskId, booked: false }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const todo = contract({ addTasks });
