import type { TraceLine, UntimedTraceLine } from "@natsuzora-dev/tazuna";
import { expect, type Page } from "@playwright/test";
import type * as Pages from "../../src/device/pages.server.ts";
import type * as Held from "../doubles/held.ts";
import { keepOpen } from "../doubles/pushedStream.ts";
import { writeTrace } from "../harness/traces.ts";
import { toSpec } from "../support/answers.ts";
import { TaskListPage } from "../support/pages/TaskListPage.ts";
import { type App, test } from "./fixtures.ts";

type DeviceRequest = Parameters<typeof Pages.sendToPage>[0];

async function playDevice(
  page: Page,
  app: App,
  held: typeof Held,
  requests: readonly DeviceRequest[],
): Promise<TraceLine[]> {
  const trace: TraceLine[] = [];
  const record = (line: UntimedTraceLine) => trace.push({ ...line, time: Temporal.Now.instant().toString() });
  const { sendToPage } = await app.runner.import<typeof Pages>("/src/device/pages.server.ts");
  const askingPermission: string[] = [];
  held.whenHeld({
    onNotificationPermission: (call) => {
      const resultOf = askingPermission.shift();
      const event: Extract<UntimedTraceLine, { type: "event" }> = {
        dir: "out",
        type: "event",
        name: toSpec.permission(call.input),
        payload: {},
      };
      record(resultOf === undefined ? event : { ...event, resultOf });
    },
    tasks: keepOpen,
    reminderSettings: keepOpen,
  });
  const connected = page.waitForResponse(`${app.url}/api/rpc/device/deviceRequests`);
  await new TaskListPage(page).goto();
  await connected;
  for (const [i, request] of requests.entries()) {
    const { name, input } = request;
    const id = `${name}-${i + 1}`;
    record({ dir: "in", type: "command", id, name, input });
    const result = await sendToPage(request);
    record({ dir: "out", type: "answer", to: id, answer: toSpec.device(result) });
    if (name === "requestNotificationPermission" && result.ok) {
      askingPermission.push(id);
      await expect.poll(() => askingPermission.includes(id)).toBe(false);
    }
  }
  return trace;
}

// In Chromium's headless shell, Notification.permission is always denied.
test("A browser without notification permission sends notificationPermissionDenied for a permission request and answers unavailable to showNotification", async ({
  page,
  app,
  held,
}) => {
  const trace = await playDevice(page, app, held, [
    { name: "requestNotificationPermission", input: {} },
    { name: "showNotification", input: { text: "Buy milk" } },
  ]);
  expect(trace).toContainEqual(expect.objectContaining({ name: "notificationPermissionDenied" }));
  expect(trace).toContainEqual(
    expect.objectContaining({
      to: "showNotification-2",
      answer: { result: "rejected", rejection: { kind: "unavailable" } },
    }),
  );
  writeTrace("device", "permissionNotGranted", trace);
});

interface PermissionSettings {
  readonly isWatched: () => boolean;
  readonly change: (state: PermissionState) => void;
}

// Chromium's headless shell does not reflect permission settings in the Permissions API, so the page's PermissionStatus
// is replaced.
test("The page sends notificationPermissionDenied when the user revokes permission in the browser settings", async ({
  page,
  app,
  held,
}) => {
  await page.addInitScript(() => {
    const status: { state: PermissionState; onchange: (() => void) | null } = { state: "granted", onchange: null };
    navigator.permissions.query = () => Promise.resolve(status as unknown as PermissionStatus);
    const settings: PermissionSettings = {
      isWatched: () => status.onchange !== null,
      change(state) {
        status.state = state;
        status.onchange?.();
      },
    };
    Reflect.set(window, "permissionSettings", settings);
  });
  const trace = await playDevice(page, app, held, []);
  await page.waitForFunction(() => (Reflect.get(window, "permissionSettings") as PermissionSettings).isWatched());
  await page.evaluate(() => (Reflect.get(window, "permissionSettings") as PermissionSettings).change("denied"));
  await expect.poll(() => trace).toContainEqual(expect.objectContaining({ name: "notificationPermissionDenied" }));
  writeTrace("device", "permissionRevoked", trace);
});

test("Closing the browser's permission prompt reports no result and shows the allow button again", async ({
  page,
  app,
  held,
}) => {
  await page.addInitScript(() => {
    Object.defineProperty(Notification, "permission", { get: () => "default" });
    Notification.requestPermission = () => {
      Reflect.set(window, "isPermissionRequested", true);
      return Promise.resolve("default");
    };
  });
  const reports: unknown[] = [];
  held.whenHeld({
    onNotificationPermission: (call) => reports.push(call.input),
    tasks: keepOpen,
    reminderSettings: keepOpen,
  });
  const { sendToPage } = await app.runner.import<typeof Pages>("/src/device/pages.server.ts");
  const connected = page.waitForResponse(`${app.url}/api/rpc/device/deviceRequests`);
  await new TaskListPage(page).goto();
  await connected;
  await sendToPage({ name: "requestNotificationPermission", input: {} });
  const allow = page.getByRole("button", { name: "Allow" });
  await allow.click();
  await page.waitForFunction(() => Reflect.get(window, "isPermissionRequested") === true);
  await expect(allow).toBeVisible();
  expect(reports).toEqual([]);
});
