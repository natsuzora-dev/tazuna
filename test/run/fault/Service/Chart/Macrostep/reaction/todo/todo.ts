import { contract, emit, entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const Stats = singleEntity({ description: "Statistics of tasks", fields: { added: z.number().default(0) } });

export const { automation, command, createEvent, updateEvent } = service({
  description: "Keep the tasks and count the titled ones",
  entities: { Task, Stats },
});

export const taskAdded = createEvent({ entity: Task });
export const statsChanged = updateEvent({ entity: Stats, writes: ["added"] });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const countAdded = command({ emits: [statsChanged] }).decide(({ records }) => [
  emit(statsChanged, { added: records.Stats.added + 1 }),
]);

export const countTitledTask = automation({
  receives: { taskAdded },
  commands: { countAdded },
}).send({
  guard: {
    titled: ({ payload }) => {
      if (payload.title === "") throw new Error("the task has no title");
      return true;
    },
  },
});

export const todo = contract({ addTask });
