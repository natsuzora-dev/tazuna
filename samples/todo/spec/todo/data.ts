import { constants, datetime, duration, entity, service, singleEntity, timeZone } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task of the user",
  fields: {
    id: z.string(),
    title: z.string().min(1).meta({ description: "The name of the task" }),
    createdAt: datetime,
    completedAt: datetime.nullable(),
    dueAt: datetime.nullable(),
    remindAt: datetime.nullable(),
    // failed: calendar returned no next business day, so no reminder time could be decided.
    reminderDecision: z.enum(["pending", "decided", "failed"]),
  },
  key: "id",
  invariants: {
    completedAfterCreated: ({ record }) =>
      record.completedAt === null || Temporal.Instant.compare(record.completedAt, record.createdAt) >= 0,
  },
});

export const Settings = singleEntity({
  description: "The setting of whether todo reminds the user of tasks",
  fields: { shouldRemind: z.boolean().default(true) },
});

// timeZone decides calendar dates; dueAheadLimit is how far ahead of now a due date may be.
export const todoConstants = constants({
  service: "todo",
  schema: z.object({ timeZone, dueAheadLimit: duration }),
  values: {
    timeZone: "Asia/Tokyo",
    dueAheadLimit: "P1Y",
  },
});

export const {
  command,
  query,
  automation,
  machine,
  event,
  createEvent,
  deleteEvent,
  updateEvent,
  contract,
  given,
  scenario,
} = service({
  name: "todo",
  description: "Keep the user's tasks and remind the user of them",
  entities: { Task, Settings },
});
