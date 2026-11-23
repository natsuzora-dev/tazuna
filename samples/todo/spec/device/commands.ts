import { z } from "zod";
import { command } from "./data.ts";
import { notificationPermissionDenied, notificationPermissionGranted } from "./events.ts";

export const requestNotificationPermission = command({
  callers: ["notifier"],
  emits: [notificationPermissionGranted, notificationPermissionDenied],
  rejects: ["unavailable"],
  ensures: { atMostOneResult: ({ events }) => events.length <= 1 },
});

/** What a notification says: a message of the app's catalog by `id`, with its values, which the app renders as text. */
const notice = z.discriminatedUnion("id", [
  z.strictObject({ id: z.literal("reminder"), values: z.strictObject({ title: z.string().min(1) }) }),
  z.strictObject({ id: z.literal("openTasks"), values: z.strictObject({ count: z.int() }) }),
]);

export const showNotification = command({
  callers: ["notifier", "todo"],
  input: { notice },
  emits: [],
  rejects: ["unavailable"],
});
