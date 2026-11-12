import { join } from "node:path";
import type { QueryAnswer } from "@natsuzora-dev/tazuna";
import type { ClientOptions } from "@orpc/client";
import { RPCLink } from "@orpc/client/fetch";
import { SimpleCsrfProtectionLinkPlugin } from "@orpc/client/plugins";
import { calendar } from "@todo/spec/calendar";
import { device } from "@todo/spec/device";
import { migrate } from "drizzle-orm/node-sqlite/migrator";
import { onTestFinished, vi } from "vitest";
import type * as Calendar from "../../src/calendar/calendar.server.ts";
import type * as Db from "../../src/db/index.server.ts";
import type * as Device from "../../src/device/device.server.ts";
import type { DeviceResult } from "../../src/device/pages.server.ts";
import type * as Notifier from "../../src/notifier/notifier.server.ts";
import { customJsonSerializers } from "../../src/orpc/serializers.ts";
import type Server from "../../src/server.ts";
import { commandRequest, type Outputs, queryRequest, type ReplayAdapter } from "../harness/replay.ts";
import { toApp, toSpec } from "./answers.ts";

interface ClientContext {
  readonly idempotencyKey?: string;
}

type Procedure = (input: unknown, options: ClientOptions<ClientContext>) => Promise<unknown>;

function todoLink(server: typeof Server) {
  return new RPCLink<ClientContext>({
    url: "http://localhost/api/rpc",
    fetch: async (request) => server.fetch(request),
    headers: ({ context }) =>
      context.idempotencyKey === undefined ? {} : { "Idempotency-Key": context.idempotencyKey },
    customJsonSerializers,
    plugins: [new SimpleCsrfProtectionLinkPlugin()],
  });
}

/** `db` is the database of the app before a restart, which the restarted app reads again. */
async function loadApp(service: "todo" | "notifier", outputs: Outputs, db?: typeof Db.db) {
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
  if (db === undefined) migrate(loaded.db, { migrationsFolder: join(import.meta.dirname, "../../drizzle") });
  return {
    db: loaded.db,
    link: todoLink((await import("../../src/server.ts")).default),
    todoRouter: (await import("../../src/todo/todo.router.ts")).todoRouter,
    events: (await import("../../src/todo/events.server.ts")).events,
    notifier: await import("../../src/notifier/notifier.server.ts"),
  };
}

export function serverAdapter(service: "todo" | "notifier"): ReplayAdapter {
  let app: Awaited<ReturnType<typeof loadApp>>;
  let outputs: Outputs;
  const load = async (db?: typeof Db.db) => {
    app = await loadApp(service, outputs, db);
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
    return (input, options) => app.link.call(["todo", name], input, options);
  };
  return {
    async start(appOutputs, time) {
      vi.useFakeTimers({ now: time.epochMilliseconds });
      onTestFinished(() => void vi.useRealTimers());
      outputs = appOutputs;
      await load();
    },
    now: () => Temporal.Now.instant(),
    async advanceTo(time) {
      const until = time.epochMilliseconds - Date.now();
      if (until > 0) await vi.advanceTimersByTimeAsync(until);
    },
    async untilQuiet(outputs, isReady) {
      for (let before = -1; before !== outputs() || !isReady(); ) {
        before = outputs();
        await vi.advanceTimersByTimeAsync(0);
      }
    },
    async command({ id, name, input }) {
      try {
        await procedure(name)(input, { context: { idempotencyKey: id } });
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
  const outputs = await subscription(input, { signal, context: {} });
  if (!isAsyncIterable(outputs)) throw new Error("the subscription answered with no event iterator");
  return outputs;
}

async function* fulfilled(outputs: AsyncIterable<unknown>): AsyncIterable<QueryAnswer> {
  for await (const output of outputs) yield { result: "fulfilled", output };
}
