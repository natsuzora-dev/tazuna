import type { ORPCErrorJSON } from "@orpc/client";
import { customType, integer, sqliteTable, text } from "drizzle-orm/sqlite-core";

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

export const notifierOpenTasks = sqliteTable("notifier_open_tasks", { taskId: text().primaryKey() });

export const notifierNotificationPermission = sqliteTable("notifier_notification_permission", {
  id: integer().primaryKey(),
  status: text({ enum: ["granted", "denied"] }).notNull(),
});

export const notifierReceivedEvents = sqliteTable("notifier_received_events", { id: text().primaryKey() });
