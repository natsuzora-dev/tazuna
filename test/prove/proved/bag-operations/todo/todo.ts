import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), points: z.int().min(0).max(10) },
  key: "id",
});

export const { command, createEvent, updateEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
  invariants: {
    boundedTotal: ({ records }) => records.Task.sum((t) => t.points) <= 30,
    mappedTotal: ({ records }) => records.Task.map((t) => t.points).sum((p) => p) <= 30,
    boundedMax: ({ records }) => (records.Task.max((t) => t.points) ?? 0) <= 10,
    boundedMin: ({ records }) => (records.Task.min((t) => t.points) ?? 0) >= 0,
    nonNegative: ({ records }) => records.Task.every((t) => t.points >= 0),
    noEleven: ({ records }) => !records.Task.some((t) => t.points === 11),
    onePerKey: ({ records }) => records.Task.filter((t) => t.id === "a").only()?.points !== 11,
  },
});

export const taskAdded = createEvent({ entity: Task });

export const pointsChanged = updateEvent({ entity: Task, writes: ["points"] });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, points: Task.fields.points },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, points: input.points })]);

export const changePoints = command({
  callers: ["client"],
  input: { taskId: ref(Task), points: Task.fields.points },
  emits: [pointsChanged],
}).decide(({ input }) => [emit(pointsChanged, { id: input.taskId, points: input.points })]);

export const todoBounds = bounds({ creates: { Task: 3 } });
