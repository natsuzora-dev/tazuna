import { datetime } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

const awaitingCompletion = { complete: () => [], reopen: () => [], delete: () => [], close: () => [] };

// While a request waits for its answer, the screen neither deletes the task nor closes, so that todo cannot receive a
// later request to the task first.
export const taskDetailScreen = screen({
  description: "The task detail screen",
  input: { taskId: todo.TaskId, placeholderTitle: todo.TaskTitle },
  // dueAt is the due date picked in the due row; null means the user removed it.
  context: {
    newTitle: todo.TaskTitle,
    dueAt: datetime.nullable().default(null),
  },
  receives: { taskDeleted: todo.taskDeleted },
  queries: { taskDetail: todo.taskDetail },
  commands: {
    completeTask: todo.completeTask,
    reopenTask: todo.reopenTask,
    renameTask: todo.renameTask,
    changeDue: todo.changeDue,
    deleteTask: todo.deleteTask,
  },
  controls: {
    rename: { label: "Title", payload: { title: todo.TaskTitle } },
    complete: { label: "Mark as complete" },
    reopen: { label: "Mark as incomplete" },
    dueToggle: { label: "Due" },
    dueChoose: { label: "Date and time", payload: { dueAt: datetime } },
    dueClear: { label: "Remove due date" },
    delete: { label: "Delete task" },
    close: { label: "Tasks" },
  },
  initial: "editing",
  states: {
    editing: {
      type: "parallel",
      states: {
        title: { initial: "viewing", states: { viewing: {}, renaming: {} } },
        completion: { initial: "ready", states: { ready: {}, completing: {}, reopening: {} } },
        due: { initial: "collapsed", states: { collapsed: {}, expanded: {}, changing: {} } },
      },
    },
    deleting: {},
    closed: { type: "final" },
  },
}).chart({
  initialContext: ({ input }) => ({ newTitle: input.placeholderTitle }),
  offers: {
    complete: ({ shown }) => (shown.taskDetail?.task?.isCompleted === false ? [{}] : []),
    reopen: ({ shown }) => (shown.taskDetail?.task?.isCompleted === true ? [{}] : []),
    dueClear: ({ shown }) => (shown.taskDetail?.task?.dueAt != null ? [{}] : []),
  },
  on: {
    close: [{ target: "closed" }],
    taskDeleted: [{ guard: { thisTask: ({ payload, input }) => payload.taskId === input.taskId }, target: "closed" }],
  },
  states: {
    editing: {
      on: { delete: [{ target: "deleting" }] },
      shows: { taskDetail: { input: ({ input }) => ({ taskId: input.taskId }) } },
    },
    viewing: {
      on: {
        rename: [
          {
            guard: { changed: ({ payload, shown }) => payload.title !== shown.taskDetail?.task?.title },
            target: "renaming",
            assign: { newTitle: ({ payload }) => payload.title },
          },
        ],
      },
    },
    renaming: {
      offers: { delete: () => [], close: () => [] },
      sends: {
        renameTask: {
          input: ({ input, context }) => ({ taskId: input.taskId, title: context.newTitle }),
          onAccepted: [{ target: "viewing" }],
          onRejected: [{ target: "viewing" }],
        },
      },
    },
    ready: { on: { complete: [{ target: "completing" }], reopen: [{ target: "reopening" }] } },
    completing: {
      offers: awaitingCompletion,
      sends: {
        completeTask: {
          input: ({ input }) => ({ taskId: input.taskId }),
          onAccepted: [{ target: "ready" }],
          onRejected: [{ target: "ready" }],
        },
      },
    },
    reopening: {
      offers: awaitingCompletion,
      sends: {
        reopenTask: {
          input: ({ input }) => ({ taskId: input.taskId }),
          onAccepted: [{ target: "ready" }],
          onRejected: [{ target: "ready" }],
        },
      },
    },
    collapsed: { offers: { dueChoose: () => [], dueClear: () => [] }, on: { dueToggle: [{ target: "expanded" }] } },
    expanded: {
      on: {
        dueToggle: [{ target: "collapsed" }],
        dueChoose: [
          {
            guard: {
              unchanged: ({ payload, shown }) => {
                const dueAt = shown.taskDetail?.task?.dueAt;
                return dueAt != null && Temporal.Instant.compare(payload.dueAt, dueAt) === 0;
              },
            },
            target: "collapsed",
          },
          {
            guard: {
              selectable: ({ payload, now }) =>
                Temporal.Instant.compare(now, payload.dueAt) < 0 &&
                Temporal.Instant.compare(
                  payload.dueAt,
                  now.toZonedDateTimeISO(todo.todoConstants.timeZone).add(todo.todoConstants.dueAheadLimit).toInstant(),
                ) <= 0,
            },
            target: "changing",
            assign: { dueAt: ({ payload }) => payload.dueAt },
          },
        ],
        dueClear: [{ target: "changing", assign: { dueAt: () => null } }],
      },
    },
    changing: {
      offers: { dueToggle: () => [], dueChoose: () => [], dueClear: () => [], delete: () => [], close: () => [] },
      sends: {
        changeDue: {
          input: ({ input, context }) => ({ taskId: input.taskId, dueAt: context.dueAt }),
          onAccepted: [{ target: "collapsed" }],
          onRejected: [{ target: "collapsed" }],
        },
      },
    },
    deleting: {
      offers: {
        rename: () => [],
        complete: () => [],
        reopen: () => [],
        dueToggle: () => [],
        dueChoose: () => [],
        dueClear: () => [],
        delete: () => [],
        close: () => [],
      },
      sends: {
        deleteTask: {
          input: ({ input }) => ({ taskId: input.taskId }),
          onAccepted: [{ target: "closed" }],
          onRejected: [{ target: "editing" }],
        },
      },
    },
  },
});
