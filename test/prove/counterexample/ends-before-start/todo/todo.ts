import { addDays, date, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), startsOn: date, endsOn: date },
  key: "id",
  invariants: { endsAfterStart: ({ record }) => record.endsOn >= record.startsOn },
});

export const { command, createEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, startsOn: date, days: z.int().min(-1).max(365) },
  emits: [taskAdded],
}).decide(({ input }) => [
  emit(taskAdded, { id: input.taskId, startsOn: input.startsOn, endsOn: addDays(input.startsOn, input.days) }),
]);

export const todoBounds = bounds({ creates: { Task: 3 } });
