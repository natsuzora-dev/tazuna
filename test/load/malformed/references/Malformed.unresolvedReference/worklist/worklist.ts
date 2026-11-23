import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { automation, command, createEvent } = service({
  name: "worklist",
  description: "Name no command from an automation and a command as an event, past the types without a written any",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { id: z.string(), title: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, input)]);

export const retryTask = command({
  callers: ["client"],
  input: { id: z.string() },
  emits: [JSON.parse("0") || addTask],
}).decide(() => []);

export const copyTask = automation({ receives: { taskAdded }, commands: JSON.parse("{}") }).send({
  input: ({ payload }) => payload,
});
