import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract } = service({ description: "Keep tasks" });

export const taskAdded = event({ payload: { taskId: z.string() } });
export const answerNoted = event({});

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const noteAnswer = command({ emits: [answerNoted] }).decide(() => [emit(answerNoted, {})]);
