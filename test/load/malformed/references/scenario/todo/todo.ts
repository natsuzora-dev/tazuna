import { any, at, cannotOperate, emit, entity, scenario, send, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });

export const { command, createEvent, screen } = service({
  description: "Keep the tasks, whose command and screen are not exported",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

const adder = screen({
  description: "A dialog that adds a task",
  controls: { cancel: { label: "Cancel" } },
  initial: "asking",
  states: { asking: {}, closed: { type: "final" } },
}).chart({ offers: { cancel: any }, states: { asking: { on: { cancel: [{ target: "closed" }] } } } });

export const addThenCancel = scenario("Add a task and cancel the dialog, both of which no export names", [
  at("2026-10-25T09:00:00+09:00"),
  send(addTask, { taskId: "task-1" }),
  cannotOperate(adder, "cancel"),
]);
