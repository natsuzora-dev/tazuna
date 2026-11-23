import { instant } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { device } from "../device/contract.ts";
import { warn } from "./commands.ts";
import { condition, machine, notifierConstants } from "./data.ts";
import { taskChangeRecorded, tooManyWarned } from "./events.ts";

// Changes and choices arrive in any order, so a task's state and the permission are the latest by `at`; a closing and
// a denial win a tie.
type Args = Parameters<Parameters<typeof condition>[0]>[0];
const openTasks = ({ records }: Args) =>
  records.TaskChange.filter(
    (c) =>
      c.change === "opened" &&
      !records.TaskChange.some(
        (d) => d.taskId === c.taskId && (d.at > c.at || (d.at === c.at && d.change === "closed")),
      ),
  );
const undetermined = condition(({ records }) => records.PermissionChoice.size === 0);
const granted = condition(({ records }) =>
  records.PermissionChoice.some(
    (g) => g.status === "granted" && !records.PermissionChoice.some((d) => d.status === "denied" && d.at >= g.at),
  ),
);

export const workload = machine({
  description: "Warn when too many tasks are open",
  commands: { warn },
  initial: "quiet",
  states: { quiet: {}, warning: {}, warned: {} },
}).chart({
  states: {
    quiet: {
      always: [
        {
          guard: { tooMany: (args) => openTasks(args).size > notifierConstants.openTaskLimit },
          target: "warning",
        },
      ],
    },
    warning: {
      sends: {
        warn: {
          input: (args) => ({ count: openTasks(args).size }),
          onAccepted: [{ target: "warned" }],
        },
      },
    },
    warned: {
      after: { periodEnd: { delay: notifierConstants.warnedPeriod, onFired: [{ target: "quiet" }] } },
    },
  },
});

const decided = condition((args) => !undetermined(args));
const hasOpenTasks = condition((args) => openTasks(args).size > 0);
const resetAttempts = { assign: { attempts: () => 0 } };
// One request goes to device at a time, since requestNotificationPermission writes the permission that
// showNotification reads. Asking does not wait for the permission that notifier knows: device answers at once when the
// user already chose, and a choice may arrive after the task that makes notifier ask.
export const notification = machine({
  description:
    "Request notification permission from the user when a task opens until a request is accepted, and show each warning as a notification if permission is granted",
  context: { attempts: z.int().default(0), count: z.int().default(0), askingSince: instant.default(0) },
  receives: { taskChangeRecorded, tooManyWarned },
  commands: {
    requestNotificationPermission: device.requestNotificationPermission,
    showNotification: device.showNotification,
  },
  initial: "starting",
  states: {
    starting: {},
    asking: {},
    notAsking: { initial: "idle", states: { idle: {}, retrying: {}, awaitingUserChoice: {}, asked: {}, showing: {} } },
  },
  invariants: {
    countsOnlyWhileRequesting: ({ context, active }) => active.asking || active.retrying || context.attempts === 0,
  },
}).chart({
  states: {
    starting: {
      always: [
        { guard: { undetermined, hasOpenTasks }, target: "asking" },
        { guard: { undetermined }, target: "idle" },
        { target: "asked" },
      ],
    },
    asking: {
      entry: { assign: { attempts: ({ context }) => context.attempts + 1, askingSince: ({ now }) => now } },
      sends: {
        requestNotificationPermission: {
          onAccepted: [{ target: "awaitingUserChoice" }],
          onRejected: [
            {
              guard: { canRetry: ({ context }) => context.attempts < notifierConstants.permissionAttempts },
              target: "retrying",
            },
            // A task that opened since the attempt began asks again, as one that opens later does in idle. Its time
            // decides, not whether it arrived before the answer; a task opened as the attempt began counts.
            {
              guard: {
                openedWhileAsking: ({ records, context }) =>
                  records.TaskChange.some((c) => c.change === "opened" && c.at >= context.askingSince),
              },
              target: "asking",
              reenter: true,
              assign: { attempts: () => 0 },
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
          { guard: { granted }, target: "showing", reenter: true, assign: { count: ({ payload }) => payload.count } },
        ],
      },
    },
    idle: {
      entry: resetAttempts,
      on: {
        taskChangeRecorded: [
          {
            guard: {
              openedSinceAsking: ({ payload, context }) =>
                payload.change === "opened" && payload.at >= context.askingSince,
            },
            target: "asking",
          },
        ],
      },
    },
    retrying: {
      always: [{ guard: { decided }, target: "asked" }],
      after: { retry: { delay: notifierConstants.permissionRetryDelay, onFired: [{ target: "asking" }] } },
    },
    awaitingUserChoice: { entry: resetAttempts, always: [{ guard: { decided }, target: "asked" }] },
    asked: { entry: resetAttempts },
    showing: {
      entry: resetAttempts,
      sends: {
        showNotification: {
          input: ({ context }) => ({ notice: { id: "openTasks", values: { count: context.count } } }),
          onAccepted: [{ target: "asked" }],
          onRejected: [{ target: "asked" }],
        },
      },
    },
  },
});
