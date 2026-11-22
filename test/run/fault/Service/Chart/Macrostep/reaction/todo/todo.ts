import { addDays, date, emit, entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), due: date }, key: "id" });

export const Stats = singleEntity({ description: "Statistics of tasks", fields: { added: z.number().default(0) } });

export const { automation, command, createEvent, updateEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks and count the ones due before year 10000",
  entities: { Task, Stats },
});

export const taskAdded = createEvent({ entity: Task });
export const statsChanged = updateEvent({ entity: Stats, writes: ["added"] });

export const addTask = command({
  input: { taskId: Task.fields.id, due: Task.fields.due },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, due: input.due })]);

export const countAdded = command({ emits: [statsChanged] }).decide(({ records }) => [
  emit(statsChanged, { added: records.Stats.added + 1 }),
]);

export const countDueTask = automation({
  receives: { taskAdded },
  commands: { countAdded },
}).send({
  guard: { dueBeforeYearTenThousand: ({ payload }) => addDays(payload.due, 3_000_000) > payload.due },
});

export const todo = contract({ addTask });
