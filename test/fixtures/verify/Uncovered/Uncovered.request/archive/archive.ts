import { bag, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const ArchivedTask = entity({
  description: "A task taken out of the backlog",
  fields: { id: z.string(), title: z.string() },
  key: "id",
});

export const { command, query, createEvent, contract } = service({
  name: "archive",
  description: "Keep the archived tasks",
  entities: { ArchivedTask },
});

export const taskArchived = createEvent({ entity: ArchivedTask });

export const archiveTask = command({
  callers: ["client"],
  input: { taskId: ArchivedTask.fields.id, title: ArchivedTask.fields.title },
  emits: [taskArchived],
}).decide(({ input }) => [emit(taskArchived, { id: input.taskId, title: input.title })]);

export const archivedTitles = query({
  callers: ["client"],
  output: { titles: bag(ArchivedTask.fields.title) },
}).resolve(({ records }) => ({ titles: records.ArchivedTask.map((t) => t.title) }));

export const archive = contract({ archiveTask, archivedTitles });
