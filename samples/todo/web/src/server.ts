import handler, { createServerEntry } from "@tanstack/react-start/server-entry";
import { onTodoEvent, startNotifier } from "./notifier/notifier.server.ts";
import { events } from "./todo/events.server.ts";
import { startReminders } from "./todo/reminders.server.ts";

// Started here, not in a Nitro plugin: Nitro bundles plugins separately, which would duplicate the src modules.
events.subscribe("todo", onTodoEvent);
startReminders();
startNotifier();

export default createServerEntry({ fetch: (request) => handler.fetch(request) });
