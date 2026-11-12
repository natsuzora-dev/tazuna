import { type DeviceResult, sendToPage } from "./pages.server.ts";

export function requestNotificationPermission(): Promise<DeviceResult> {
  return sendToPage({ name: "requestNotificationPermission", input: {} });
}

export function showNotification(input: { readonly text: string }): Promise<DeviceResult> {
  return sendToPage({ name: "showNotification", input });
}
