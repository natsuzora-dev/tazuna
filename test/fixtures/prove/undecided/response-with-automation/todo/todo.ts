import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), assignee: z.string().nullable() },
  key: "id",
  responses: {
    assigned: {
      when: ({ record }) => record.assignee === null,
      expect: ({ record }) => record.assignee !== null,
      within: 3_600_000,
    },
  },
});

export const { command, automation, createEvent, updateEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks, each assigned to the bot once added",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const taskAssigned = updateEvent({ entity: Task, writes: ["assignee"] });

export const addTask = command({ callers: ["client"], input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId, assignee: null })],
);

export const assignTask = command({
  callers: ["todo"],
  input: { taskId: ref(Task), assignee: z.string() },
  emits: [taskAssigned],
}).decide(({ input }) => [emit(taskAssigned, { id: input.taskId, assignee: input.assignee })]);

export const assignToBot = automation({ receives: { taskAdded }, commands: { assignTask } }).send({
  input: ({ payload }) => ({ taskId: payload.id, assignee: "bot" }),
});

export const todoBounds = bounds({ creates: { Task: 2 } });
