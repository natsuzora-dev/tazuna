import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { notes } from "../notes/contract.ts";

export const { automation, command, event, contract, scenario } = service({
  name: "todo",
  description: "Keep the list",
});

export const taskAdded = event({ payload: { title: z.string() } });

export const addTask = command({ input: { title: z.string() }, emits: [taskAdded] }).decide(({ input }) => [
  emit(taskAdded, input),
]);

export const noteAdded = automation({
  receives: { taskAdded },
  commands: { addNote: notes.addNote },
}).send({ input: ({ payload }) => ({ text: payload.title }), onRejected: [] });
