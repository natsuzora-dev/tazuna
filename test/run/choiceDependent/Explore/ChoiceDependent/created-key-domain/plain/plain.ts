import { bag, emit, entity, ref, service, singleEntity } from "@natsuzora-dev/tazuna";
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

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const addTask = command({
  input: { taskId: Task.fields.id, text: Task.fields.text },
  emits: [taskAdded, counted],
}).decide(({ input, records }) => [
  emit(taskAdded, { id: input.taskId, text: input.text }),
  emit(counted, { n: records.Count.n + 1 }),
]);

export const taskIds = query({
  output: { taskIds: bag(Task.fields.id) },
}).resolve(({ records }) => ({ taskIds: records.Task.map((t) => t.id) }));

const clock = (text: string) =>
  machine({
    description: `Add task ${text} at 10:00 once armed`,
    receives: { armed },
    commands: { addTask },
    initial: "idle",
    states: { idle: {}, waiting: {}, adding: {}, done: { type: "final" } },
  }).chart({
    states: {
      idle: { on: { armed: [{ target: "waiting" }] } },
      waiting: {
        after: { due: { at: () => Temporal.Instant.from("2026-10-25T01:00:00Z"), onFired: [{ target: "adding" }] } },
      },
      adding: {
        sends: {
          addTask: {
            input: ({ createKey }) => ({ taskId: createKey(ref(Task)), text }),
            onAccepted: [{ target: "done" }],
            onRejected: [{ target: "done" }],
          },
        },
      },
    },
  });

export const first = clock("a");
export const second = clock("b");

export const plain = contract({ arm, taskIds });
