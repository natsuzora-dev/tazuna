import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";

export const OpenTask = entity({
  description: "A task that is not completed",
  fields: { taskId: z.string() },
  key: "taskId",
});

export const { automation, command, createEvent, contract, scenario } = service({
  name: "notifier",
  description: "Notify tasks",
  entities: { OpenTask },
});

export const openTaskRecorded = createEvent({ entity: OpenTask });

export const recordOpenTask = command({
  input: { taskId: OpenTask.fields.taskId },
  emits: [openTaskRecorded],
}).decide(({ input, records }) =>
  records.OpenTask.get(input.taskId) === undefined ? [emit(openTaskRecorded, { taskId: input.taskId })] : [],
);

export const recordAddedTask = automation({
  receives: { taskAdded: todo.taskAdded },
  commands: { recordOpenTask },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });
