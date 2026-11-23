import { z } from "zod";
import { createEvent, event, PermissionChoice, TaskChange } from "./data.ts";

export const tooManyWarned = event({
  payload: { count: z.int() },
});

export const taskChangeRecorded = createEvent({
  entity: TaskChange,
});

export const permissionChoiceRecorded = createEvent({
  entity: PermissionChoice,
});
