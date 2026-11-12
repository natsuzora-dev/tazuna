import { z } from "zod";
import { command } from "./data.ts";
import { notificationPermissionDenied, notificationPermissionGranted } from "./events.ts";

export const requestNotificationPermission = command({
  emits: [notificationPermissionGranted, notificationPermissionDenied],
  rejects: ["unavailable"],
  ensures: { atMostOneResult: ({ events }) => events.length <= 1 },
});

export const showNotification = command({ input: { text: z.string().min(1) }, emits: [], rejects: ["unavailable"] });
