import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), assignee: z.string().nullable() },
  key: "id",
  responses: {
    assignedBeforeAdded: {
      when: ({ record }) => record.assignee === null,
      expect: ({ record }) => record.assignee !== null,
      within: -1,
    },
    assignedInHalfAMillisecond: {
      when: ({ record }) => record.assignee === null,
      expect: ({ record }) => record.assignee !== null,
      within: 0.5,
    },
    assignedAtOnce: {
      when: ({ record }) => record.assignee === null,
      expect: ({ record }) => record.assignee !== null,
      within: 0,
    },
  },
});

export const { command, createEvent, contract } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({ callers: ["client"], input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId, assignee: null })],
);

export const todo = contract({ addTask });
