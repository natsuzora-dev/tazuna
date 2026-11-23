import { z } from "zod";
import { createEvent, deleteEvent, event, NotificationPermission, OpenTask, updateEvent } from "./data.ts";

export const tooManyWarned = event({
  payload: { count: z.int() },
});

export const openTaskRecorded = createEvent({
  entity: OpenTask,
});

export const openTaskForgotten = deleteEvent({
  entity: OpenTask,
});

export const notificationPermissionRecorded = updateEvent({
  entity: NotificationPermission,
  writes: ["status"],
});
