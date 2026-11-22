import { emit, entity, parseInstant, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), text: z.string() }, key: "id" });

export const { command, machine, event, createEvent, contract, scenario } = service({
  name: "tracker",
  description: "Add a task with a created key from each of two clocks at 10:00, and track the task added first",
  entities: { Task },
});

export const armed = event({});
export const added = createEvent({ entity: Task });

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const add = command({ input: { id: Task.fields.id, text: Task.fields.text }, emits: [added] }).decide(
  ({ input }) => [emit(added, { id: input.id, text: input.text })],
);

export const first = machine({
  description: `Add task a at 10:00 once armed`,
  receives: { armed },
  commands: { add },
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
        add: {
          input: ({ createKey }) => ({ id: createKey(ref(Task)), text: "a" }),
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
  commands: { add },
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
        add: {
          input: ({ createKey }) => ({ id: createKey(ref(Task)), text: "b" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const tracking = machine({
  description: "Track the first added task in the parameters of watching",
  receives: { added },
  initial: "idle",
  states: { idle: {}, watching: { held: { taskId: ref(Task) } } },
}).chart({
  states: {
    idle: { on: { added: [{ target: "watching", with: { taskId: ({ payload }) => payload.id } }] } },
  },
});

export const tracker = contract({ arm });
