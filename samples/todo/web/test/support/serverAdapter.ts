import { join } from "node:path";
import { setImmediate as afterPendingCallbacks } from "node:timers/promises";
import type { QueryAnswer } from "@natsuzora-dev/tazuna";
import {
  type Adapter,
  commandRequest,
  type GivenRecord,
  type Outputs,
  queryRequest,
} from "@natsuzora-dev/tazuna/verify";
import { createRouterClient } from "@orpc/server";
import { calendar } from "@todo/spec/calendar";
import { device } from "@todo/spec/device";
import { migrate } from "drizzle-orm/node-sqlite/migrator";
import { onTestFinished, vi } from "vitest";
import type * as Calendar from "../../src/calendar/calendar.server.ts";
import type * as Db from "../../src/db/index.server.ts";
import * as schema from "../../src/db/schema.ts";
import type * as Device from "../../src/device/device.server.ts";
import type { DeviceResult } from "../../src/device/pages.server.ts";
import type * as Notifier from "../../src/notifier/notifier.server.ts";
import { toApp, toSpec } from "./answers.ts";

interface CallOptions {
  readonly idempotencyKey?: string;
  readonly signal?: AbortSignal;
}

type Procedure = (input: unknown, options: CallOptions) => Promise<unknown>;

const instant = (value: unknown) => (typeof value === "number" ? value : null);

/** Writes the Given records into the app's database, as the app stores them. */
function seed(db: typeof Db.db, records: readonly GivenRecord[]): void {
  for (const { entity, value } of records) {
    const row = value as Record<string, unknown>;
    switch (entity) {
      case "Task":
        db.insert(schema.tasks)
          .values({
            id: String(row["id"]),
            title: String(row["title"]),
            createdAt: Number(row["createdAt"]),
            completedAt: instant(row["completedAt"]),
            dueAt: instant(row["dueAt"]),
            remindAt: instant(row["remindAt"]),
            reminderDecision: row["reminderDecision"] as "pending" | "decided" | "failed",
          })
          .run();
        break;
      case "Settings":
        db.insert(schema.settings)
          .values({ id: 1, shouldRemind: row["shouldRemind"] === true })
          .run();
        break;
      case "OpenTask":
        db.insert(schema.notifierOpenTasks)
          .values({ taskId: String(row["taskId"]) })
          .run();
        break;
      case "NotificationPermission":
        if (row["status"] === "granted" || row["status"] === "denied")
          db.insert(schema.notifierNotificationPermission).values({ id: 1, status: row["status"] }).run();
        break;
      default:
        throw new Error(`the app stores no ${entity} records`);
    }
  }
}

/**
 * `db` is the database of the app before a restart, which the restarted app reads again; a new database holds the
 * Given `records` before the app starts.
 */
async function loadApp(
  service: "todo" | "notifier",
  outputs: Outputs,
  db: typeof Db.db | undefined,
  records: readonly GivenRecord[],
) {
  const calendarDouble: typeof Calendar = {
    nextBusinessDay: (input) =>
      new Promise((resolve) =>
        outputs.request(queryRequest(calendar.nextBusinessDay, input, (a) => resolve(toApp.calendar(a)))),
      ),
  };
  const deviceRequest = (name: keyof typeof Device, input: object) =>
    new Promise<DeviceResult>((resolve) =>
      outputs.request(commandRequest(device[name], input, (a) => resolve(toApp.device(a)))),
    );
  const deviceDouble: typeof Device = {
    requestNotificationPermission: () => deviceRequest("requestNotificationPermission", {}),
    showNotification: (input) => deviceRequest("showNotification", input),
  };
  const notifierDouble: typeof Notifier = {
    onTodoEvent: () => {},
    onNotificationPermission: () => {},
    startNotifier: () => {},
  };
  vi.resetModules();
  vi.doMock(import("../../src/calendar/calendar.server.ts"), () => calendarDouble);
  vi.doMock(import("../../src/device/device.server.ts"), () => deviceDouble);
  if (service === "todo") vi.doMock(import("../../src/notifier/notifier.server.ts"), () => notifierDouble);
  if (db === undefined) vi.doUnmock(import("../../src/db/index.server.ts"));
  else vi.doMock(import("../../src/db/index.server.ts"), () => ({ db }));
  const loaded = await import("../../src/db/index.server.ts");
  if (db === undefined) {
    migrate(loaded.db, { migrationsFolder: join(import.meta.dirname, "../../drizzle") });
    seed(loaded.db, records);
  }
  return {
    db: loaded.db,
    // The server module starts the event subscriptions, reminders and notifier that the app runs beside its router.
    server: await import("../../src/server.ts"),
    todoRouter: (await import("../../src/todo/todo.router.ts")).todoRouter,
    events: (await import("../../src/todo/events.server.ts")).events,
    notifier: await import("../../src/notifier/notifier.server.ts"),
  };
}

export function serverAdapter(service: "todo" | "notifier"): Adapter {
  let app: Awaited<ReturnType<typeof loadApp>>;
  let outputs: Outputs;
  const load = async (db?: typeof Db.db, records: readonly GivenRecord[] = []) => {
    app = await loadApp(service, outputs, db, records);
    app.events.subscribe("todo", outputs.event);
  };
  // A restarted server keeps no timers or requests of the previous process but reads the same database.
  // vi.clearAllTimers rewinds the clock to the fake timers' start, so the time is set again.
  const restart = () => {
    const now = Date.now();
    vi.clearAllTimers();
    vi.setSystemTime(now);
    return load(app.db);
  };
  const procedure = (name: string): Procedure => {
    if (!Object.hasOwn(app.todoRouter, name)) throw new Error(`the app implements no ${name}`);
    // The router runs in this process without HTTP, so the app's work is callbacks and fake timers that settled sees.
    return (input, { idempotencyKey, signal }) => {
      const headers = new Headers(idempotencyKey === undefined ? {} : { "Idempotency-Key": idempotencyKey });
      type Call = (input: unknown, options: { readonly signal?: AbortSignal | undefined }) => Promise<unknown>;
      const client = createRouterClient(app.todoRouter, { context: { headers } }) as unknown as Record<string, Call>;
      return (client[name] as Call)(input, { signal });
    };
  };
  return {
    async start(appOutputs, time, records) {
      vi.useFakeTimers({ now: time });
      onTestFinished(() => void vi.useRealTimers());
      outputs = appOutputs;
      await load(undefined, records);
    },
    now: () => Date.now(),
    async advanceTo(time) {
      const until = time - Date.now();
      if (until > 0) await vi.advanceTimersByTimeAsync(until);
    },
    // The app does its work in callbacks and fake timers, so it has settled when running the timers due now and then
    // every pending callback (a real setImmediate runs after them) schedules no timer.
    async settled() {
      for (let timers = -1; timers !== vi.getTimerCount(); ) {
        await vi.advanceTimersByTimeAsync(0);
        timers = vi.getTimerCount();
        await afterPendingCallbacks();
      }
    },
    async command({ id, name, input }) {
      try {
        await procedure(name)(input, { idempotencyKey: id });
        return { result: "accepted" };
      } catch (error) {
        return toSpec.rejected(error);
      }
    },
    async query({ name, input }) {
      const controller = new AbortController();
      try {
        for await (const output of await answers(procedure(name), input, controller.signal))
          return { result: "fulfilled", output };
        throw new Error(`the subscription ${name} ended without an answer`);
      } catch (error) {
        return toSpec.rejected(error);
      } finally {
        controller.abort();
      }
    },
    async subscribe({ name, input }, signal) {
      try {
        return fulfilled(await answers(procedure(name), input, signal));
      } catch (error) {
        return [toSpec.rejected(error)];
      }
    },
    restart,
    receive(event) {
      const granted = toApp.permission(event.name);
      if (granted === undefined) app.notifier.onTodoEvent(toApp.todoEvent(event));
      else app.notifier.onNotificationPermission(granted);
    },
  };
}

const isAsyncIterable = (value: unknown): value is AsyncIterable<unknown> =>
  typeof value === "object" && value !== null && Symbol.asyncIterator in value;

async function answers(subscription: Procedure, input: unknown, signal: AbortSignal): Promise<AsyncIterable<unknown>> {
  const outputs = await subscription(input, { signal });
  if (!isAsyncIterable(outputs)) throw new Error("the subscription answered with no event iterator");
  return outputs;
}

async function* fulfilled(outputs: AsyncIterable<unknown>): AsyncIterable<QueryAnswer> {
  for await (const output of outputs) yield { result: "fulfilled", output };
}
