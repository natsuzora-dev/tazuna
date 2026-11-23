import type { ORPCErrorJSON } from "@orpc/client";
import { customType, integer, primaryKey, sqliteTable, text } from "drizzle-orm/sqlite-core";

const instant = customType<{ data: number; driverData: string }>({
  dataType: () => "text",
  toDriver: (ms) => Temporal.Instant.fromEpochMilliseconds(ms).toString(),
  fromDriver: (text) => Temporal.Instant.from(text).epochMilliseconds,
});

export const tasks = sqliteTable("tasks", {
  id: text().primaryKey(),
  title: text().notNull(),
  createdAt: instant().notNull(),
  completedAt: instant(),
  dueAt: instant(),
  remindAt: instant(),
  reminderDecision: text({ enum: ["pending", "decided", "failed"] }).notNull(),
});

export const settings = sqliteTable("settings", {
  id: integer().primaryKey(),
  shouldRemind: integer({ mode: "boolean" }).notNull(),
});

export type StoredAnswer = { readonly output: unknown } | { readonly error: ORPCErrorJSON<string, unknown> };

export const commandAnswers = sqliteTable("command_answers", {
  key: text().primaryKey(),
  request: text().notNull(),
  answer: text({ mode: "json" }).$type<StoredAnswer>().notNull(),
});

export const notifierTaskChanges = sqliteTable(
  "notifier_task_changes",
  { taskId: text().notNull(), at: instant().notNull(), change: text({ enum: ["opened", "closed"] }).notNull() },
  (t) => [primaryKey({ columns: [t.taskId, t.at, t.change] })],
);

export const notifierPermissionChoices = sqliteTable(
  "notifier_permission_choices",
  { status: text({ enum: ["granted", "denied"] }).notNull(), at: instant().notNull() },
  (t) => [primaryKey({ columns: [t.status, t.at] })],
);
