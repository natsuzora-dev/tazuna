import { contract } from "@natsuzora-dev/tazuna";
import { requestNotificationPermission, showNotification } from "./commands.ts";
import { notificationPermissionDenied, notificationPermissionGranted } from "./events.ts";

export const device = contract({
  requestNotificationPermission,
  showNotification,
  notificationPermissionGranted,
  notificationPermissionDenied,
});
