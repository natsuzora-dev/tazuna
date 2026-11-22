import { notifierConstants } from "@todo/spec/notifier";
import { eq } from "drizzle-orm";
import { db } from "../db/index.server.ts";
import { notifierNotificationPermission, notifierOpenTasks, notifierReceivedEvents } from "../db/schema.ts";
import { requestNotificationPermission, showNotification } from "../device/device.server.ts";
import type { TodoEvent } from "../todo/events.server.ts";

export function onTodoEvent(event: TodoEvent): void {
  const first = db.insert(notifierReceivedEvents).values({ id: event.id }).onConflictDoNothing().run().changes > 0;
  if (!first) return;
  switch (event.name) {
    case "taskAdded":
    case "taskReopened":
      recordOpenTask(event.payload.taskId);
      return;
    case "taskCompleted":
    case "taskDeleted":
      db.delete(notifierOpenTasks).where(eq(notifierOpenTasks.taskId, event.payload.taskId)).run();
      return;
  }
}

export function onNotificationPermission(granted: boolean): void {
  const status = granted ? "granted" : "denied";
  db.insert(notifierNotificationPermission)
    .values({ id: 1, status })
    .onConflictDoUpdate({ target: notifierNotificationPermission.id, set: { status } })
    .run();
  if (flow === "retrying" || flow === "awaitingUserChoice") toIdle();
}

export function startNotifier(): void {
  warnIfTooMany();
  if (permissionStatus() === "undetermined" && db.$count(notifierOpenTasks).sync() > 0) void askPermission();
}

const permissionStatus = () => db.select().from(notifierNotificationPermission).get()?.status ?? "undetermined";

function recordOpenTask(taskId: string): void {
  const recordedNow = db.insert(notifierOpenTasks).values({ taskId }).onConflictDoNothing().run().changes > 0;
  if (!recordedNow) return;
  if (warnedPeriod === undefined) warnIfTooMany();
  else startWarnedPeriod();
  if (flow === "idle" && permissionStatus() === "undetermined") void askPermission();
}

let warnedPeriod: ReturnType<typeof setTimeout> | undefined;

function warnIfTooMany(): void {
  const count = db.$count(notifierOpenTasks).sync();
  if (count <= notifierConstants.openTaskLimit) return;
  showWarning(count);
  startWarnedPeriod();
}

function startWarnedPeriod(): void {
  clearTimeout(warnedPeriod);
  warnedPeriod = setTimeout(() => {
    warnedPeriod = undefined;
    warnIfTooMany();
  }, notifierConstants.warnedPeriod);
}

// One request goes to device at a time, since requestNotificationPermission writes the permission that
// showNotification reads.
let flow: "idle" | "asking" | "retrying" | "awaitingUserChoice" = "idle";
let attempts = 0;
let retry: ReturnType<typeof setTimeout> | undefined;

function toIdle(): void {
  clearTimeout(retry);
  flow = "idle";
  attempts = 0;
}

function showWarning(count: number): void {
  if (flow === "asking" || permissionStatus() !== "granted") return;
  void showNotification({ text: `You have ${count} open tasks` });
}

async function askPermission(): Promise<void> {
  flow = "asking";
  attempts += 1;
  const answer = await requestNotificationPermission();
  if (permissionStatus() !== "undetermined") {
    toIdle();
  } else if (answer.ok) {
    flow = "awaitingUserChoice";
    attempts = 0;
  } else if (attempts < notifierConstants.permissionAttempts) {
    flow = "retrying";
    retry = setTimeout(askPermission, notifierConstants.permissionRetryDelay);
  } else {
    toIdle();
  }
}
