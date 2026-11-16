import { requestNotificationPermission, showNotification } from "./commands.ts";
import { contract } from "./data.ts";
import { notificationPermissionDenied, notificationPermissionGranted } from "./events.ts";

export const device = contract({
  requestNotificationPermission,
  showNotification,
  notificationPermissionGranted,
  notificationPermissionDenied,
});
