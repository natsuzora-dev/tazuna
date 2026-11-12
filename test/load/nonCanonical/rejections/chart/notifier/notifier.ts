import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";

export const { command, event, machine } = service({ description: "Notify about tasks" });

export const followUpAdded = event({ payload: { taskId: z.string() } });

export const addFollowUp = command({
  input: { taskId: z.string() },
  emits: [followUpAdded],
}).decide(({ input }) => [emit(followUpAdded, { taskId: input.taskId })]);

export const followUp = machine({
  description: "Add a task for each follow-up",
  receives: { followUpAdded },
  commands: { addTask: todo.addTask },
  initial: "idle",
  states: { idle: {}, adding: {} },
}).chart({
  states: {
    idle: { on: { followUpAdded: [{ target: "adding" }] } },
    adding: { sends: { addTask: { input: () => ({ taskId: "task-2" }), onAccepted: [{ target: "idle" }] } } },
  },
});
