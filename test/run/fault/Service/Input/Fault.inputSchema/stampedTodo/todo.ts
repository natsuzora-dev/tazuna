import { datetime, emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { automation, command, event, scenario } = service({
  name: "stampedTodo",
  description: "Remind the tasks",
});

const due: Temporal.Instant = JSON.parse('"2026-10-26T00:00:00Z"');

export const taskAdded = event({ payload: { taskId: z.string() } });
export const reminderSet = event({ payload: { taskId: z.string() } });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { taskId: input.taskId })]);

export const setReminder = command({
  input: { taskId: z.string(), at: datetime },
  emits: [reminderSet],
}).decide(({ input }) => [emit(reminderSet, { taskId: input.taskId })]);

export const remind = automation({
  receives: { taskAdded },
  commands: { setReminder },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId, at: due }) });
