import { constants, duration, entity, instant, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task of the user",
  fields: {
    id: z.string(),
    title: z.string().min(1).meta({ description: "The name of the task" }),
    createdAt: instant,
    completedAt: instant.nullable(),
    dueAt: instant.nullable(),
    remindAt: instant.nullable(),
    // failed: calendar returned no next business day, so no reminder time could be decided.
    reminderDecision: z.enum(["pending", "decided", "failed"]),
  },
  key: "id",
  invariants: {
    completedAfterCreated: ({ record }) => record.completedAt === null || record.completedAt >= record.createdAt,
  },
});

export const Settings = singleEntity({
  description: "The setting of whether todo reminds the user of tasks",
  fields: { shouldRemind: z.boolean().default(true) },
});

// dueAheadLimit is how far ahead of now a due date may be: 365 days.
export const todoConstants = constants({
  service: "todo",
  schema: z.object({ dueAheadLimit: duration }),
  values: { dueAheadLimit: 365 * 86_400_000 },
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
