import { and, eq, isNotNull, isNull } from "drizzle-orm";
import { nextBusinessDay } from "../calendar/calendar.server.ts";
import { changes, notifyChange } from "../changes.server.ts";
import { db } from "../db/index.server.ts";
import { tasks } from "../db/schema.ts";
import { showNotification } from "../device/device.server.ts";
import { readReminderSettings } from "./queries.server.ts";

const calendarRequests = new Map<string, object>();

export async function decideReminderTime(taskId: string): Promise<void> {
  const request = {};
  calendarRequests.set(taskId, request);
  const result = await nextBusinessDay({ after: Date.now() });
  if (calendarRequests.get(taskId) !== request) return;
  calendarRequests.delete(taskId);
  db.update(tasks)
    .set(result.ok ? { remindAt: result.startsAt, reminderDecision: "decided" } : { reminderDecision: "failed" })
    .where(eq(tasks.id, taskId))
    .run();
  notifyChange();
}

export function stopDecidingReminderTime(taskId: string): void {
  calendarRequests.delete(taskId);
}

/** Node's setTimeout turns a longer delay into 1 ms. */
const longestDelay = 2 ** 31 - 1;
let timer: ReturnType<typeof setTimeout> | undefined;

function setReminderTimer(): void {
  clearTimeout(timer);
  const next = openTasksWithReminder()
    .map((t) => t.remindAt)
    .toSorted((a, b) => a - b)[0];
  if (next === undefined) return;
  const delay = next - Date.now();
  timer = setTimeout(remindDueTasks, Math.min(Math.max(delay, 0), longestDelay));
}

function openTasksWithReminder() {
  return db
    .select()
    .from(tasks)
    .where(and(isNull(tasks.completedAt), isNotNull(tasks.remindAt)))
    .all()
    .flatMap((t) => (t.remindAt === null ? [] : [{ ...t, remindAt: t.remindAt }]));
}

function remindDueTasks(): void {
  const now = Date.now();
  const due = openTasksWithReminder().filter((t) => t.remindAt <= now);
  const { shouldRemind } = readReminderSettings();
  for (const task of due) {
    db.update(tasks).set({ remindAt: null }).where(eq(tasks.id, task.id)).run();
    if (shouldRemind) void showNotification({ text: task.title });
  }
  notifyChange();
}

export function startReminders(): void {
  changes.subscribe("changed", setReminderTimer);
  setReminderTimer();
  for (const { id } of db.select({ id: tasks.id }).from(tasks).where(eq(tasks.reminderDecision, "pending")).all())
    void decideReminderTime(id);
}
