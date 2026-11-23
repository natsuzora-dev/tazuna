import { notifierConstants } from "@todo/spec/notifier";
import { db } from "../db/index.server.ts";
import { notifierPermissionChoices, notifierTaskChanges } from "../db/schema.ts";
import { requestNotificationPermission, showNotification } from "../device/device.server.ts";
import type { TodoEvent } from "../todo/events.server.ts";

export function onTodoEvent(event: TodoEvent): void {
  const { taskId, at } = event.payload;
  const change = event.name === "taskAdded" || event.name === "taskReopened" ? "opened" : "closed";
  const recorded =
    db.insert(notifierTaskChanges).values({ taskId, at, change }).onConflictDoNothing().run().changes > 0;
  if (!recorded || change === "closed") return;
  if (flow === "idle" && at >= askingSince) void askPermission();
  if (warnedPeriod === undefined) warnIfTooMany();
}

export function onNotificationPermission({ granted, at }: { readonly granted: boolean; readonly at: number }): void {
  const status = granted ? "granted" : "denied";
  const recorded = db.insert(notifierPermissionChoices).values({ status, at }).onConflictDoNothing().run().changes > 0;
  if (recorded && (flow === "retrying" || flow === "awaitingUserChoice")) toAsked();
}

export function startNotifier(): void {
  if (!isDecided()) {
    if (openTaskCount() > 0) void askPermission();
  } else flow = "asked";
  warnIfTooMany();
}

// Changes and choices arrive in any order, so a task's state and the permission are the latest by time; a closing and
// a denial win a tie.
function openTaskCount(): number {
  const changes = db.select().from(notifierTaskChanges).all();
  return changes.filter(
    (c) =>
      c.change === "opened" &&
      !changes.some((d) => d.taskId === c.taskId && (d.at > c.at || (d.at === c.at && d.change === "closed"))),
  ).length;
}

const openedSince = (start: number) =>
  db
    .select()
    .from(notifierTaskChanges)
    .all()
    .some((c) => c.change === "opened" && c.at >= start);

const isDecided = () => db.$count(notifierPermissionChoices).sync() > 0;

function isGranted(): boolean {
  const choices = db.select().from(notifierPermissionChoices).all();
  return choices.some((g) => g.status === "granted" && !choices.some((d) => d.status === "denied" && d.at >= g.at));
}

let warnedPeriod: ReturnType<typeof setTimeout> | undefined;

function warnIfTooMany(): void {
  const count = openTaskCount();
  if (count <= notifierConstants.openTaskLimit) return;
  showWarning(count);
  warnedPeriod = setTimeout(() => {
    warnedPeriod = undefined;
    warnIfTooMany();
  }, notifierConstants.warnedPeriod);
}

// One request goes to device at a time, since requestNotificationPermission writes the permission that
// showNotification reads. Asking does not wait for the permission that notifier knows: device answers at once when the
// user already chose, and a choice may arrive after the task that makes notifier ask.
let flow: "idle" | "asking" | "retrying" | "awaitingUserChoice" | "asked" | "showing" = "idle";
let attempts = 0;
let askingSince = 0;
let retry: ReturnType<typeof setTimeout> | undefined;

function toAsked(): void {
  clearTimeout(retry);
  flow = "asked";
  attempts = 0;
}

function showWarning(count: number): void {
  if (flow === "asking" || !isGranted()) return;
  clearTimeout(retry);
  flow = "showing";
  attempts = 0;
  void showNotification({ notice: { id: "openTasks", values: { count } } }).then(() => {
    if (flow === "showing") flow = "asked";
  });
}

async function askPermission(): Promise<void> {
  flow = "asking";
  attempts += 1;
  askingSince = Date.now();
  const answer = await requestNotificationPermission();
  if (answer.ok) {
    if (isDecided()) toAsked();
    else {
      flow = "awaitingUserChoice";
      attempts = 0;
    }
  } else if (attempts < notifierConstants.permissionAttempts) {
    if (isDecided()) toAsked();
    else {
      flow = "retrying";
      retry = setTimeout(askPermission, notifierConstants.permissionRetryDelay);
    }
  } else if (openedSince(askingSince)) {
    // A task that opened during the attempt asks again, as one that opens after them does.
    attempts = 0;
    void askPermission();
  } else {
    flow = "idle";
    attempts = 0;
  }
}
