import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, contract } = service({ description: "Keep the tasks" });

export const taskAdded = event({ payload: { title: z.string() } });

export const addTask = command({ input: { title: z.string() }, emits: [taskAdded] }).decide(({ input }) => [
  emit(taskAdded, { title: input.title }),
]);

export const todo = contract({ addTask });
