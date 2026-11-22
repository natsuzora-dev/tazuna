import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event, contract } = service({ name: "todo", description: "Keep the tasks" });

export const tasksNumbered = event({ payload: { titles: z.array(z.string()) } });

export const numberTasks = command({ input: { titles: z.array(z.string()) }, emits: [tasksNumbered] }).decide(
  ({ input }) => [emit(tasksNumbered, { titles: input.titles.map((title, i) => `${i + 1}. ${title}`) })],
);

export const todo = contract({ numberTasks });
