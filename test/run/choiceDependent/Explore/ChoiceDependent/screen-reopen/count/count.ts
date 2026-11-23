import { bag, emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, screen, event, contract, scenario } = service({
  name: "count",
  description: "A panel opens a detail, and claimed reopens it",
});

export const taskAdded = event({ payload: { id: z.string() } });

export const addTasks = command({
  callers: ["client"],
  input: { taskIds: bag(z.string()) },
  emits: [taskAdded],
}).decide(({ input }) => [input.taskIds.map((id) => emit(taskAdded, { id }))]);

export const claimed = event({});
export const claim = command({ callers: ["client", "count"], emits: [claimed] }).decide(() => [emit(claimed, {})]);

export const helper = screen({
  description: "Claims once on the first task",
  receives: { taskAdded },
  commands: { claim },
  initial: "idle",
  states: { idle: {}, claiming: {}, done: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "claiming" }] } },
    claiming: { sends: { claim: { onAccepted: [{ target: "done" }] } } },
  },
});

export const detailScreen = screen({
  description: "A detail",
  initial: "showing",
  states: { showing: {} },
}).chart({});

export const panel = screen({
  description: "Opens a detail on task a, closes it on task b, and reopens it on claimed",
  receives: { taskAdded, claimed },
  screens: { detailScreen },
  initial: "idle",
  states: { idle: {}, open: {}, left: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ guard: { isA: ({ payload }) => payload.id === "a" }, target: "open" }] } },
    open: {
      on: {
        taskAdded: [{ guard: { isB: ({ payload }) => payload.id === "b" }, target: "left" }],
        claimed: [{ target: "open", reenter: true }],
      },
      opens: { detailScreen: { modal: false, onDone: [] } },
    },
    left: { on: { claimed: [{ target: "open" }] } },
  },
});

export const countContract = contract({ addTasks });
