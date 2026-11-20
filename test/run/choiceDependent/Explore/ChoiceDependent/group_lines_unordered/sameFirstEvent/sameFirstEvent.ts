import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Count = singleEntity({ description: "A count", fields: { seen: z.number().default(0) } });

export const { automation, command, machine, event, updateEvent, contract, scenario } = service({
  name: "sameFirstEvent",
  description: "Count the task-1 events that arrive before task-3",
  entities: { Count },
});

export const started = event({});
export const taskAdded = event({ payload: { id: z.string() } });
export const counted = updateEvent({ entity: Count, writes: ["seen"] });

export const start = command({ emits: [started] }).decide(() => [emit(started, {})]);

export const addTwo = command({ emits: [taskAdded] }).decide(() => [
  emit(taskAdded, { id: "task-1" }),
  emit(taskAdded, { id: "task-2" }),
]);

export const addThree = command({ emits: [taskAdded] }).decide(() => [
  emit(taskAdded, { id: "task-1" }),
  emit(taskAdded, { id: "task-3" }),
]);

export const set = command({ input: { seen: z.number() }, emits: [counted] }).decide(({ input }) => [
  emit(counted, { seen: input.seen }),
]);

export const withTwo = automation({ receives: { started }, commands: { addTwo } }).send({});

export const withThree = automation({ receives: { started }, commands: { addThree } }).send({});

export const counter = machine({
  description: "Count task-1 events until task-3 arrives, then write the count",
  context: { seen: z.number().default(0) },
  receives: { taskAdded },
  commands: { set },
  initial: "counting",
  states: { counting: {}, setting: {}, done: {} },
}).chart({
  states: {
    counting: {
      on: {
        taskAdded: [
          { guard: { isThird: ({ payload }) => payload.id === "task-3" }, target: "setting" },
          {
            guard: { isFirst: ({ payload }) => payload.id === "task-1" },
            assign: { seen: ({ context }) => context.seen + 1 },
          },
        ],
      },
    },
    setting: {
      sends: {
        set: { input: ({ context }) => ({ seen: context.seen }), onAccepted: [{ target: "done" }], onRejected: [] },
      },
    },
  },
});

export const sameFirstEventContract = contract({ start });
