import { constants, duration, entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";

export const notifierConstants = constants(
  "notifier",
  z.object({
    openTaskLimit: z.int(),
    warnedPeriod: duration,
    permissionAttempts: z.int(),
    permissionRetryDelay: duration,
  }),
  { openTaskLimit: 10, warnedPeriod: "PT1H", permissionAttempts: 3, permissionRetryDelay: "PT1M" },
);

export const OpenTask = entity({
  description: "An open task of todo",
  fields: { taskId: todo.TaskId },
  key: "taskId",
});

export const NotificationPermission = singleEntity({
  description: "The notification permission that device reported last",
  fields: { status: z.enum(["undetermined", "granted", "denied"]).default("undetermined") },
});

export const { command, automation, machine, event, createEvent, deleteEvent, updateEvent, contract, scenario } =
  service({
    name: "notifier",
    description: "Notify the user about open tasks, with the notification permission that it requests",
    entities: { OpenTask, NotificationPermission },
  });
