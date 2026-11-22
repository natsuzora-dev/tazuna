import { any, emit, entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string() },
  key: "id",
  invariants: {},
});

export const Settings = singleEntity({
  description: "The settings",
  fields: { shouldRemind: z.boolean().default(true) },
  invariants: {},
});

export const { automation, command, query, event, machine, screen, createEvent, contract } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task, Settings },
  invariants: {},
});

export const taskAdded = createEvent({ entity: Task });
export const pinged = event({ payload: {} });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const ping = command({ input: {}, emits: [pinged], binds: {}, requires: {}, ensures: {} }).decide(() => [
  emit(pinged, {}),
]);

export const tasks = query({ input: {}, output: { count: z.number() }, requires: {}, ensures: {} }).resolve(
  ({ records }) => ({ count: records.Task.size }),
);

export const pingOnAdd = automation({ receives: { taskAdded }, commands: { ping } }).send({ binds: {}, guard: {} });

export const reminderWithoutEmptyKeywords = machine({
  description: "Wait an hour after each added task",
  receives: { taskAdded },
  initial: "idle",
  states: { idle: {}, waiting: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "waiting" }] } },
    waiting: { after: { hour: { delay: 3_600_000, onFired: [{ target: "idle" }] } } },
  },
});

export const reminder = machine({
  description: "Wait an hour after each added task, writing its empty keywords as {}",
  context: {},
  receives: { taskAdded },
  queries: {},
  commands: { ping },
  initial: "idle",
  states: { idle: {}, waiting: { held: {} }, done: {} },
  invariants: {},
}).chart({
  on: {},
  states: {
    idle: { on: { taskAdded: [{ guard: {}, target: "waiting" }] }, after: {}, calls: {} },
    waiting: {
      sends: { ping: { onAccepted: [{ target: "idle", assign: {} }] } },
      entry: { assign: {} },
    },
    done: {},
  },
});

export const listScreen = screen({
  description: "List the tasks, writing its empty keywords as {}",
  input: {},
  output: {},
  context: {},
  receives: {},
  queries: {},
  commands: {},
  screens: {},
  controls: { refresh: { label: "Refresh", payload: {} } },
  initial: "showing",
  states: { showing: {} },
  requires: {},
  ensures: {},
  invariants: {},
}).chart({
  offers: { refresh: any },
  states: { showing: { shows: {}, opens: {}, on: { refresh: [{ target: "showing", reenter: true }] } } },
});

export const todo = contract({ addTask, tasks });
