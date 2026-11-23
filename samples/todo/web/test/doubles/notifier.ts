import type * as Notifier from "../../src/notifier/notifier.server.ts";
import { hold } from "./held.ts";

export const onTodoEvent: typeof Notifier.onTodoEvent = (event) => void hold("onTodoEvent", event, undefined);
export const onNotificationPermission: typeof Notifier.onNotificationPermission = (choice) =>
  void hold("onNotificationPermission", choice, undefined);
export const startNotifier: typeof Notifier.startNotifier = () => {};
