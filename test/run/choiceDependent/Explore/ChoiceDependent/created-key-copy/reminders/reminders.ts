import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), text: z.string() }, key: "id" });

export const { command, machine, event, createEvent, contract, scenario } = service({
  name: "reminders",
  description:
    "Add a task with a created key from each of two clocks at 10:00, and remind of each task at a time its text sets",
  entities: { Task },
});

export const armed = event({});
export const added = createEvent({ entity: Task });

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const add = command({ input: { id: Task.fields.id, text: Task.fields.text }, emits: [added] }).decide(
  ({ input }) => [emit(added, { id: input.id, text: input.text })],
);

const clock = (text: string) =>
  machine({
    description: `Add task ${text} at 10:00 once armed`,
    receives: { armed },
    commands: { add },
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
          add: {
            input: ({ createKey }) => ({ id: createKey(ref(Task)), text }),
            onAccepted: [{ target: "done" }],
            onRejected: [{ target: "done" }],
          },
        },
      },
    },
  });

export const first = clock("a");
export const second = clock("b");

export const reminder = machine({
  description: "Remind of each task, task a at 12:00 and the others at 13:00",
  initial: "tasks",
  states: {
    tasks: { type: "map", key: { taskId: ref(Task) }, initial: "waiting", states: { waiting: {}, reminded: {} } },
  },
}).chart({
  states: {
    tasks: { items: ({ records }) => records.Task.map((t) => ({ taskId: t.id })) },
    waiting: {
      after: {
        remind: {
          at: ({ key, records }) =>
            Temporal.Instant.from(
              records.Task.get(key.taskId)?.text === "a" ? "2026-10-25T03:00:00Z" : "2026-10-25T04:00:00Z",
            ),
          onFired: [{ target: "reminded" }],
        },
      },
    },
  },
});

export const reminders = contract({ arm });
