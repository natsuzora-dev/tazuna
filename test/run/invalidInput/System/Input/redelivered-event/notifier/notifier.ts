import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const Seen = entity({ description: "A task the notifier saw", fields: { taskId: todo.TaskId }, key: "taskId" });

export const { automation, command, createEvent } = service({ description: "Notify about tasks", entities: { Seen } });

export const seen = createEvent({ entity: Seen });

export const see = command({
  input: { taskId: Seen.fields.taskId },
  emits: [seen],
}).decide(({ input, records }) =>
  records.Seen.get(input.taskId) === undefined ? [emit(seen, { taskId: input.taskId })] : [],
);

export const seeAdded = automation({
  receives: { taskAdded: todo.taskAdded },
  commands: { see },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }) });
