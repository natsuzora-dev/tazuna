import { any, none } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";
import { taskDetailScreen } from "./taskDetailScreen.ts";

const Selected = z.object({ taskId: todo.TaskId, title: todo.TaskTitle });
const Filter = todo.tasks.input.filter;
// While a request waits for its answer, the list accepts no operation: test pairs concurrent requests by definition,
// not by task, so a request to another task would be compared as one to the same task.
const awaitingList = {
  openTask: none,
  add: none,
  remindersToggle: none,
  complete: none,
  reopen: none,
};

// While a request waits for its answer, the screen takes no other operation that sends a request, so that todo
// receives the requests in the order the user made them.
export const taskListScreen = screen({
  description: "The task list screen",
  context: {
    filter: Filter.default("open"),
  },
  queries: { tasks: todo.tasks, reminderSettings: todo.reminderSettings },
  commands: {
    addTask: todo.addTask,
    completeTask: todo.completeTask,
    reopenTask: todo.reopenTask,
    changeReminders: todo.changeReminders,
  },
  screens: { taskDetail: taskDetailScreen },
  controls: {
    filter: { label: "Filter", payload: { filter: Filter } },
    openTask: { label: "Open task", payload: { taskId: todo.TaskId, title: todo.TaskTitle } },
    add: { label: "Add", payload: { title: todo.TaskTitle } },
    complete: { label: "Mark as complete", payload: { taskId: todo.TaskId } },
    reopen: { label: "Mark as incomplete", payload: { taskId: todo.TaskId } },
    remindersToggle: {
      label: "Reminders",
      payload: { shouldRemind: todo.changeReminders.input.shouldRemind },
    },
  },
  initial: "showing",
  states: {
    showing: {
      initial: "listing",
      states: {
        listing: {},
        adding: { held: { title: todo.TaskTitle } },
        changingReminders: { held: { shouldRemind: todo.changeReminders.input.shouldRemind } },
        completing: { held: { taskId: todo.TaskId } },
        reopening: { held: { taskId: todo.TaskId } },
        detail: { held: { selected: Selected } },
      },
    },
  },
}).chart({
  offers: {
    filter: any,
    add: any,
    openTask: ({ shown }) => (shown.tasks?.tasks ?? []).map((t) => ({ taskId: t.taskId, title: t.title })),
    complete: ({ shown }) =>
      (shown.tasks?.tasks ?? []).filter((t) => t.completedAt === null).map((t) => ({ taskId: t.taskId })),
    reopen: ({ shown }) =>
      (shown.tasks?.tasks ?? []).filter((t) => t.completedAt !== null).map((t) => ({ taskId: t.taskId })),
    remindersToggle: ({ shown }) =>
      shown.reminderSettings == null ? [] : [{ shouldRemind: !shown.reminderSettings.shouldRemind }],
  },
  states: {
    showing: {
      on: { filter: [{ assign: { filter: ({ payload }) => payload.filter } }] },
      shows: { reminderSettings: {}, tasks: { input: ({ context }) => ({ filter: context.filter }) } },
    },
    listing: {
      on: {
        openTask: [{ target: "detail", with: { selected: ({ payload }) => payload } }],
        add: [{ target: "adding", with: { title: ({ payload }) => payload.title } }],
        remindersToggle: [
          { target: "changingReminders", with: { shouldRemind: ({ payload }) => payload.shouldRemind } },
        ],
        complete: [{ target: "completing", with: { taskId: ({ payload }) => payload.taskId } }],
        reopen: [{ target: "reopening", with: { taskId: ({ payload }) => payload.taskId } }],
      },
    },
    adding: {
      offers: awaitingList,
      sends: {
        addTask: {
          input: ({ held, createKey }) => ({ taskId: createKey(todo.TaskId), title: held.title }),
          onAccepted: [{ target: "listing" }],
          onRejected: [{ target: "listing" }],
        },
      },
    },
    changingReminders: {
      offers: awaitingList,
      sends: {
        changeReminders: {
          input: ({ held }) => ({ shouldRemind: held.shouldRemind }),
          onAccepted: [{ target: "listing" }],
          onRejected: [{ target: "listing" }],
        },
      },
    },
    completing: {
      offers: awaitingList,
      sends: {
        completeTask: {
          input: ({ held }) => ({ taskId: held.taskId }),
          onAccepted: [{ target: "listing" }],
          onRejected: [{ target: "listing" }],
        },
      },
    },
    reopening: {
      offers: awaitingList,
      sends: {
        reopenTask: {
          input: ({ held }) => ({ taskId: held.taskId }),
          onAccepted: [{ target: "listing" }],
          onRejected: [{ target: "listing" }],
        },
      },
    },
    detail: {
      opens: {
        taskDetail: {
          modal: true,
          input: ({ held }) => ({ taskId: held.selected.taskId, placeholderTitle: held.selected.title }),
          onDone: [{ target: "listing" }],
        },
      },
    },
  },
});
