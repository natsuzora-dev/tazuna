import { constants, duration, entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";

export const notifierConstants = constants({
  service: "notifier",
  schema: z.object({
    openTaskLimit: z.int(),
    warnedPeriod: duration,
    permissionAttempts: z.int(),
    permissionRetryDelay: duration,
  }),
  values: { openTaskLimit: 10, warnedPeriod: 3_600_000, permissionAttempts: 3, permissionRetryDelay: 60_000 },
});

export const OpenTask = entity({
  description: "An open task of todo",
  fields: { taskId: todo.TaskId },
  key: "taskId",
});

export const NotificationPermission = singleEntity({
  description: "The notification permission that device reported last",
  fields: { status: z.enum(["undetermined", "granted", "denied"]).default("undetermined") },
});

export const {
  command,
  automation,
  machine,
  event,
  createEvent,
  deleteEvent,
  updateEvent,
  contract,
  given,
  scenario,
  condition,
} = service({
  name: "notifier",
  description: "Notify the user about open tasks, with the notification permission that it requests",
  entities: { OpenTask, NotificationPermission },
});
