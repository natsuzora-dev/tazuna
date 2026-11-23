import { addDays, date, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), due: date }, key: "id" });

export const { command, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
  invariants: {
    dueBeforeYearTenThousand: ({ records }) => records.Task.every((task) => addDays(task.due, 3_000_000) > task.due),
  },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, due: Task.fields.due },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, due: input.due })]);

export const todo = contract({ addTask });
