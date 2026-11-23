import { constants, duration, entity, instant, service } from "@natsuzora-dev/tazuna";
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

export const TaskChange = entity({
  description:
    "A change of a todo task that todo reported, at the time todo made it: opened when added or reopened, closed when completed or deleted",
  fields: { taskId: todo.TaskId, at: instant, change: z.enum(["opened", "closed"]) },
  key: ["taskId", "at", "change"],
});

export const PermissionChoice = entity({
  description: "A notification permission that the user chose on device, at the time of the choice",
  fields: { status: z.enum(["granted", "denied"]), at: instant },
  key: ["status", "at"],
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
  bounds,
} = service({
  name: "notifier",
  description: "Notify the user about open tasks, with the notification permission that it requests",
  entities: { TaskChange, PermissionChoice },
});
