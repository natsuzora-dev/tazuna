import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { automation, command, event, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks and note each added one",
});

export const taskAdded = event({ payload: { taskId: z.string() } });
export const noted = event({});

export const addTask = command({ input: { taskId: z.string() }, emits: [taskAdded] }).decide(({ input }) => [
  emit(taskAdded, { taskId: input.taskId }),
]);

export const note = command({ emits: [noted] }).decide(() => [emit(noted, {})]);

export const noteAdded = automation({ receives: { taskAdded }, commands: { note } }).send({});
