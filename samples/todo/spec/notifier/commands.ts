import { emit } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { command, PermissionChoice, TaskChange } from "./data.ts";
import { permissionChoiceRecorded, taskChangeRecorded, tooManyWarned } from "./events.ts";

export const warn = command({ callers: ["notifier"], input: { count: z.int() }, emits: [tooManyWarned] }).decide(
  ({ input }) => [emit(tooManyWarned, { count: input.count })],
);

export const recordTaskChange = command({
  callers: ["notifier"],
  input: { taskId: TaskChange.fields.taskId, at: TaskChange.fields.at, change: TaskChange.fields.change },
  emits: [taskChangeRecorded],
}).decide(({ input, records }) =>
  records.TaskChange.get(input) === undefined
    ? [emit(taskChangeRecorded, { taskId: input.taskId, at: input.at, change: input.change })]
    : [],
);

export const recordPermissionChoice = command({
  callers: ["notifier"],
  input: { status: PermissionChoice.fields.status, at: PermissionChoice.fields.at },
  emits: [permissionChoiceRecorded],
}).decide(({ input, records }) =>
  records.PermissionChoice.get(input) === undefined
    ? [emit(permissionChoiceRecorded, { status: input.status, at: input.at })]
    : [],
);
