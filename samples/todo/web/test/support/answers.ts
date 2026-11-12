import type { CommandAnswer, QueryAnswer, Rejection } from "@natsuzora-dev/tazuna";
import { ORPCError } from "@orpc/client";
import type { calendar } from "@todo/spec/calendar";
import type { device } from "@todo/spec/device";
import { todo } from "@todo/spec/todo";
import { z } from "zod";
import type { CalendarResult } from "../../src/calendar/calendar.server.ts";
import type { DeviceResult } from "../../src/device/pages.server.ts";
import { commandErrors } from "../../src/todo/errors.ts";
import type { TodoEvent } from "../../src/todo/events.server.ts";
import type { InputMessage } from "../harness/replay.ts";

function errorTable<T extends Readonly<Record<string, Rejection>>>(rejections: T) {
  const byError = new Map<string, Rejection>(Object.entries(rejections));
  return {
    rejection(error: string): Rejection {
      const rejection = byError.get(error);
      if (rejection === undefined) throw new Error(`the spec has no rejection for the app's error ${error}`);
      return rejection;
    },
    error({ kind, reason }: Rejection) {
      for (const error in rejections)
        if (rejections[error]?.kind === kind && rejections[error]?.reason === reason) return error;
      throw new Error(`the app has no error for ${kind} ${reason ?? ""}`);
    },
  };
}

const rpcErrors = errorTable({
  TASK_ALREADY_EXISTS: { kind: "already-exists" },
  TASK_NOT_FOUND: { kind: "not-found" },
  ALREADY_COMPLETED: { kind: "requires", reason: "notCompleted" },
  NOT_COMPLETED: { kind: "requires", reason: "completed" },
  DUE_IN_PAST: { kind: "requires", reason: "notPast" },
  IDEMPOTENCY_KEY_REUSED: { kind: "reused-id" },
  BAD_REQUEST: { kind: "invalid-input" },
  INTERNAL_SERVER_ERROR: { kind: "unavailable" },
} satisfies Record<keyof typeof commandErrors | "BAD_REQUEST" | "INTERNAL_SERVER_ERROR", Rejection>);

const statuses = new Map(Object.entries(commandErrors).map(([code, { status }]) => [code, status]));

function rejected(error: unknown): { readonly result: "rejected"; readonly rejection: Rejection } {
  if (error instanceof ORPCError) return { result: "rejected", rejection: rpcErrors.rejection(error.code) };
  throw error;
}

function commandErrorToApp(answer: CommandAnswer): ORPCError<string, unknown> | undefined {
  if (answer.result !== "rejected") return undefined;
  const code = rpcErrors.error(answer.rejection);
  const status = statuses.get(code);
  return status === undefined ? new ORPCError(code) : new ORPCError(code, { status });
}

const eventNames = <N extends string>(names: { readonly [K in N]: K }) => z.enum(names);

const todoEventName = eventNames<TodoEvent["name"]>({
  taskAdded: "taskAdded",
  taskCompleted: "taskCompleted",
  taskReopened: "taskReopened",
  taskDeleted: "taskDeleted",
});

function todoEventToApp({ id, name, payload }: InputMessage): TodoEvent {
  const event = todoEventName.parse(name.replace(/^todo\./, ""));
  return { id, name: event, payload: z.object(todo[event].payload).parse(payload) };
}

const calendarErrors = errorTable({ unavailable: { kind: "unavailable" } });

type NextBusinessDay = typeof calendar.nextBusinessDay;

const calendarToApp = (answer: QueryAnswer<z.output<z.ZodObject<NextBusinessDay["output"]>>>): CalendarResult =>
  answer.result === "rejected"
    ? { ok: false, error: calendarErrors.error(answer.rejection) }
    : { ok: true, day: answer.output.day };

const calendarToSpec = (result: CalendarResult): QueryAnswer =>
  result.ok
    ? { result: "fulfilled", output: { day: result.day } }
    : { result: "rejected", rejection: calendarErrors.rejection(result.error) };

const deviceErrors = errorTable({ unavailable: { kind: "unavailable" } });

const deviceToSpec = (result: DeviceResult): CommandAnswer =>
  result.ok ? { result: "accepted" } : { result: "rejected", rejection: deviceErrors.rejection(result.error) };

const deviceToApp = (answer: CommandAnswer): DeviceResult =>
  answer.result === "rejected" ? { ok: false, error: deviceErrors.error(answer.rejection) } : { ok: true };

type Device = typeof device;
type DeviceEvent = { [K in keyof Device]: Device[K] extends { readonly kind: "event" } ? K : never }[keyof Device];

const deviceEventName = eventNames<DeviceEvent>({
  notificationPermissionGranted: "notificationPermissionGranted",
  notificationPermissionDenied: "notificationPermissionDenied",
});

const permissionEvent = z.templateLiteral(["device.", deviceEventName]);

export const toSpec = {
  rejected,
  calendar: calendarToSpec,
  device: deviceToSpec,
  permission: (isGranted: boolean): DeviceEvent =>
    isGranted ? deviceEventName.enum.notificationPermissionGranted : deviceEventName.enum.notificationPermissionDenied,
};

export const toApp = {
  commandError: commandErrorToApp,
  todoEvent: todoEventToApp,
  calendar: calendarToApp,
  device: deviceToApp,
  permission(name: string): boolean | undefined {
    const event = permissionEvent.safeParse(name);
    return event.success ? event.data === "device.notificationPermissionGranted" : undefined;
  },
};
