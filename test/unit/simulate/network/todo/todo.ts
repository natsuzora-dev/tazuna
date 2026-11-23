import { any, bag, emit, entity, ref, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { calendar } from "../calendar/contract.ts";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), seen: z.boolean() },
  key: "id",
  invariants: { titled: ({ record }) => record.title !== "" },
});

export const Booking = entity({ description: "A booking of a slot", fields: { id: z.string() }, key: "id" });

export const Settings = singleEntity({
  description: "How todo reminds",
  fields: { remind: z.boolean().default(true) },
});

export const { automation, command, createEvent, event, machine, query, screen, updateEvent, contract } = service({
  name: "todo",
  description: "Keep the tasks and book a slot for each",
  entities: { Task, Booking, Settings },
});

export const taskAddedRecorded = createEvent({ entity: Task });
export const taskSeenRecorded = updateEvent({ entity: Task, writes: ["seen"] });
export const taskAdded = event({ payload: { taskId: Task.fields.id } });
export const pinged = event({});
export const noted = event({});

export const addTask = command({
  callers: ["client", "calendar"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAddedRecorded, taskAdded],
}).decide(({ input }) => [
  emit(taskAddedRecorded, { id: input.taskId, title: input.title, seen: false }),
  emit(taskAdded, { taskId: input.taskId }),
]);

export const addTasks = command({
  callers: ["client"],
  input: { firstId: Task.fields.id, secondId: Task.fields.id },
  emits: [taskAddedRecorded, taskAdded],
}).decide(({ input }) => [
  emit(taskAddedRecorded, { id: input.firstId, title: input.firstId, seen: false }),
  emit(taskAdded, { taskId: input.firstId }),
  emit(taskAddedRecorded, { id: input.secondId, title: input.secondId, seen: false }),
  emit(taskAdded, { taskId: input.secondId }),
]);

export const markSeen = command({
  callers: ["client", "notifier"],
  input: { taskId: ref(Task) },
  emits: [taskSeenRecorded],
}).decide(({ input }) => [emit(taskSeenRecorded, { id: input.taskId, seen: true })]);

export const ping = command({ callers: ["client", "notifier"], emits: [pinged] }).decide(() => [emit(pinged, {})]);

export const note = command({ callers: ["client", "todo"], emits: [noted] }).decide(() => [emit(noted, {})]);

export const noteAdded = automation({ receives: { taskAdded }, commands: { note } }).send({});

export const tasks = query({
  callers: ["client"],
  output: { tasks: bag(z.object({ taskId: ref(Task), seen: Task.fields.seen })) },
}).resolve(({ records }) => ({ tasks: records.Task.map((t) => ({ taskId: t.id, seen: t.seen })) }));

export const booking = machine({
  description: "Book a slot for each added task, one at a time",
  receives: { taskAdded, bookingConfirmed: calendar.bookingConfirmed },
  commands: { book: calendar.book },
  context: { taskId: z.string().default("") },
  initial: "idle",
  states: { idle: {}, asking: {}, booked: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "asking", assign: { taskId: ({ payload }) => payload.taskId } }] } },
    asking: {
      sends: {
        book: {
          input: ({ context, createKey }) => ({ bookingId: createKey(ref(Booking)), taskId: context.taskId }),
          onAccepted: [{ target: "booked" }],
          onRejected: [{ target: "idle" }],
        },
      },
    },
    booked: { on: { bookingConfirmed: [{ target: "idle" }] } },
  },
});

export const morning = machine({
  description: "Wait an hour after todo begins",
  initial: "waiting",
  states: { waiting: {}, done: {} },
}).chart({ states: { waiting: { after: { hour: { delay: 3_600_000, onFired: [{ target: "done" }] } } } } });

export const evening = machine({
  description: "Wait an hour after todo begins, as morning does",
  initial: "waiting",
  states: { waiting: {}, done: {} },
}).chart({ states: { waiting: { after: { hour: { delay: 3_600_000, onFired: [{ target: "done" }] } } } } });

export const listScreen = screen({
  description: "A screen that stays open until the user closes it",
  controls: { close: { label: "Close" } },
  initial: "listing",
  states: { listing: {}, closed: { type: "final" } },
}).chart({
  offers: { close: any },
  states: { listing: { on: { close: [{ target: "closed" }] } } },
});
