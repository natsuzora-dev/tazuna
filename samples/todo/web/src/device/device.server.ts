import { type DeviceResult, sendToPage } from "./pages.server.ts";

export function requestNotificationPermission(): Promise<DeviceResult> {
  return sendToPage({ name: "requestNotificationPermission", input: {} });
}

type ShowNotification = Extract<Parameters<typeof sendToPage>[0], { readonly name: "showNotification" }>;

export function showNotification(input: ShowNotification["input"]): Promise<DeviceResult> {
  return sendToPage({ name: "showNotification", input });
}
