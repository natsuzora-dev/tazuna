import { bag, emit, entity, parseInstant, ref, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), text: z.string() }, key: "id" });

export const Count = singleEntity({ description: "Tasks added", fields: { n: z.int().default(0) } });

export const { command, query, machine, event, createEvent, updateEvent, contract, scenario } = service({
  name: "plain",
  description: "Two clocks each add a task with a created key at 10:00",
  entities: { Task, Count },
});

export const armed = event({});
export const taskAdded = createEvent({ entity: Task });
export const counted = updateEvent({ entity: Count, writes: ["n"] });

export const arm = command({ callers: ["client"], emits: [armed] }).decide(() => [emit(armed, {})]);

export const addTask = command({
  callers: ["client", "plain"],
  input: { taskId: Task.fields.id, text: Task.fields.text },
  emits: [taskAdded, counted],
}).decide(({ input, records }) => [
  emit(taskAdded, { id: input.taskId, text: input.text }),
  emit(counted, { n: records.Count.n + 1 }),
]);

export const taskIds = query({ callers: ["client"], output: { taskIds: bag(Task.fields.id) } }).resolve(
  ({ records }) => ({ taskIds: records.Task.map((t) => t.id) }),
);

export const first = machine({
  description: `Add task a at 10:00 once armed`,
  receives: { armed },
  commands: { addTask },
  initial: "idle",
  states: { idle: {}, waiting: {}, adding: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "adding" }] } },
    },
    adding: {
      sends: {
        addTask: {
          input: ({ createKey }) => ({ taskId: createKey(ref(Task)), text: "a" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const second = machine({
  description: `Add task b at 10:00 once armed`,
  receives: { armed },
  commands: { addTask },
  initial: "idle",
  states: { idle: {}, waiting: {}, adding: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "adding" }] } },
    },
    adding: {
      sends: {
        addTask: {
          input: ({ createKey }) => ({ taskId: createKey(ref(Task)), text: "b" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const plain = contract({ arm, taskIds });
