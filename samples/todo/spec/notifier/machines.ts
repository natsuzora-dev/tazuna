import { z } from "zod";
import { device } from "../device/contract.ts";
import { warn } from "./commands.ts";
import { condition, machine, notifierConstants } from "./data.ts";
import { openTaskRecorded, tooManyWarned } from "./events.ts";

export const workload = machine({
  description: "Warn when too many tasks are open",
  receives: { openTaskRecorded },
  commands: { warn },
  initial: "quiet",
  states: { quiet: {}, warning: {}, warned: {} },
}).chart({
  states: {
    quiet: {
      always: [
        {
          guard: { tooMany: ({ records }) => records.OpenTask.size > notifierConstants.openTaskLimit },
          target: "warning",
        },
      ],
    },
    warning: {
      sends: {
        warn: {
          input: ({ records }) => ({ count: records.OpenTask.size }),
          onAccepted: [{ target: "warned" }],
        },
      },
    },
    warned: {
      on: { openTaskRecorded: [{ target: "warned", reenter: true }] },
      after: { periodEnd: { delay: notifierConstants.warnedPeriod, onFired: [{ target: "quiet" }] } },
    },
  },
});

const undetermined = condition(({ records }) => records.NotificationPermission.status === "undetermined");

const decided = condition((args) => !undetermined(args));

const hasOpenTasks = condition(({ records }) => records.OpenTask.size > 0);

const resetAttempts = { assign: { attempts: () => 0 } };

// One request goes to device at a time, since requestNotificationPermission writes the permission that
// showNotification reads.
export const notification = machine({
  description:
    "Request notification permission from the user while it is undetermined, and show each warning as a notification if permission is granted",
  context: { attempts: z.number().default(0), count: z.number().default(0) },
  receives: { openTaskRecorded, tooManyWarned },
  commands: {
    requestNotificationPermission: device.requestNotificationPermission,
    showNotification: device.showNotification,
  },
  initial: "starting",
  states: {
    starting: {},
    asking: {},
    notAsking: { initial: "idle", states: { idle: {}, retrying: {}, awaitingUserChoice: {}, showing: {} } },
  },
  invariants: {
    countsOnlyWhileRequesting: ({ context, active }) => active.asking || active.retrying || context.attempts === 0,
  },
}).chart({
  states: {
    starting: { always: [{ guard: { undetermined, hasOpenTasks }, target: "asking" }, { target: "idle" }] },
    asking: {
      entry: { assign: { attempts: ({ context }) => context.attempts + 1 } },
      sends: {
        requestNotificationPermission: {
          onAccepted: [{ target: "awaitingUserChoice" }],
          onRejected: [
            {
              guard: { canRetry: ({ context }) => context.attempts < notifierConstants.permissionAttempts },
              target: "retrying",
            },
            { target: "idle" },
          ],
        },
      },
    },
    notAsking: {
      on: {
        // Without permission the device shows no notification, as with the Web Notification API.
        tooManyWarned: [
          {
            guard: { granted: ({ records }) => records.NotificationPermission.status === "granted" },
            target: "showing",
            reenter: true,
            assign: { count: ({ payload }) => payload.count },
          },
        ],
      },
    },
    idle: { entry: resetAttempts, on: { openTaskRecorded: [{ guard: { undetermined }, target: "asking" }] } },
    retrying: {
      always: [{ guard: { decided }, target: "idle" }],
      after: { retry: { delay: notifierConstants.permissionRetryDelay, onFired: [{ target: "asking" }] } },
    },
    awaitingUserChoice: { entry: resetAttempts, always: [{ guard: { decided }, target: "idle" }] },
    showing: {
      entry: resetAttempts,
      sends: {
        showNotification: {
          input: ({ context }) => ({ text: `You have ${context.count} open tasks` }),
          onAccepted: [{ target: "idle" }],
          onRejected: [{ target: "idle" }],
        },
      },
    },
  },
});
