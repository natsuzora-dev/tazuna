import {
  type AnswerOf,
  type Caused,
  endOf,
  external,
  notOffered,
  type OutRequest,
  offered,
  type RequestOf,
  request,
  requested,
  run,
  type ScreenRef,
  subscription,
  type When,
} from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { taskDetailScreen } from "./taskDetailScreen.ts";
import { taskListScreen } from "./taskListScreen.ts";

const milkRecord = {
  id: "task-1",
  title: "Buy milk",
  createdAt: "2026-10-25T08:00:00+09:00",
  completedAt: null,
  dueAt: "2026-10-26T18:00:00+09:00",
  remindAt: "2026-10-26T18:00:00+09:00",
  reminderDecision: "decided",
} as const;
const completedEggsRecord = {
  id: "task-2",
  title: "Buy eggs",
  createdAt: "2026-10-25T08:00:00+09:00",
  completedAt: "2026-10-25T09:00:00+09:00",
  dueAt: null,
  remindAt: null,
  reminderDecision: "failed",
} as const;

const givenTasks = (Task: readonly (typeof milkRecord | typeof completedEggsRecord)[]) =>
  ({
    start: "2026-10-25T10:00:00+09:00",
    records: {},
    peers: {
      todo: run(todo, { Task, Settings: { shouldRemind: true } }),
      // todo's run asks calendar when a task's reminder becomes pending.
      calendar: external(calendar),
    },
  }) as const;
const milk = givenTasks([milkRecord]);
const milkAndCompletedEggs = givenTasks([milkRecord, completedEggsRecord]);
type W = When<typeof milk.peers>;

const accepted = { result: "accepted" } as const;
const fulfilled = <O>(output: O) => ({ result: "fulfilled", output }) as const;

const milkRow = { taskId: "task-1", title: "Buy milk", dueAt: "2026-10-26T18:00:00+09:00", completedAt: null } as const;
const completedMilkRow = { ...milkRow, completedAt: "2026-10-25T10:00:00+09:00" } as const;
const completedEggsRow = {
  taskId: "task-2",
  title: "Buy eggs",
  dueAt: null,
  completedAt: "2026-10-25T09:00:00+09:00",
} as const;
const milkDetail = {
  title: "Buy milk",
  isCompleted: false,
  dueAt: "2026-10-26T18:00:00+09:00",
  createdAt: "2026-10-25T08:00:00+09:00",
  remindAt: "2026-10-26T18:00:00+09:00",
} as const;

type List = ScreenRef<typeof taskListScreen>;
type Detail = ScreenRef<typeof taskDetailScreen>;

/** The network delivers the screens' request to todo, and todo's answer to it reaches the screens. */
const delivered = <T extends RequestOf<typeof todo>>(w: W, req: OutRequest<T>, answer: AnswerOf<T>) => {
  w.net.deliver(req);
  return w.peer.todo.answer(req, answer);
};

/** The list screen that begin opens, its two subscriptions, and todo's first answers to them. */
const openList = (w: W) => {
  const list: List = w.begin.screen(taskListScreen);
  const tasksSub = w.begin.request(todo.tasks);
  const settingsSub = w.begin.request(todo.reminderSettings);
  delivered(w, tasksSub, fulfilled({ tasks: [milkRow] }));
  delivered(w, settingsSub, fulfilled({ shouldRemind: true }));
  return { list, tasksSub, settingsSub };
};

/** The user opens task-1 from `list`; returns the detail screen and its subscription. */
const openTask = (w: W, list: List) => {
  const opening = w.user.operate(list, "openTask", { taskId: "task-1", title: "Buy milk" });
  const detail: Detail = opening.screen(taskDetailScreen);
  return { detail, detailSub: opening.request(todo.taskDetail) };
};

/** openList, then the detail screen of task-1 showing todo's answer. */
const openDetail = (w: W) => {
  const opened = openList(w);
  const { detail, detailSub } = openTask(w, opened.list);
  delivered(w, detailSub, fulfilled({ task: milkDetail }));
  return { ...opened, detail, detailSub };
};

/**
 * The request of `target` that `line` caused reaches todo, and todo's answer reaches the screens. Returns the request
 * and the line that delivered it, whose processing in todo caused todo's own requests.
 */
const reply = <T extends RequestOf<typeof todo>>(w: W, line: Caused, target: T, answer: AnswerOf<T>) => {
  const req = line.request(target);
  const reached = w.net.deliver(req);
  w.peer.todo.answer(req, answer);
  return { req, reached };
};

/** reply, and todo's events that result from the request are still in flight at the end. */
const replyEmitting = <T extends RequestOf<typeof todo>>(w: W, line: Caused, target: T, answer: AnswerOf<T>) => {
  const replied = reply(w, line, target, answer);
  w.net.inFlight(replied.req);
  return replied;
};

/** The network fails to deliver the request of `target` that `line` caused, and the screens get unavailable. */
const unreachable = (w: W, line: Caused, target: RequestOf<typeof todo>) => w.net.fail(line.request(target));

/** todo's later messages on these requests are still in flight when the scenario ends. */
const inFlight = (w: W, ...requests: readonly OutRequest[]) => {
  for (const r of requests) w.net.inFlight(r);
};

export const addTask = scenario(
  "Enter a title in the new task field of the list screen and press add; the screen sends addTask",
  {
    given: milk,
    when: (w) => {
      const { list, tasksSub } = openList(w);
      const adding = w.user.operate(list, "add", { title: "Buy eggs" });
      const { req: sent, reached: addingReached } = replyEmitting(w, adding, todo.addTask, accepted);
      w.peer.calendar.leaveUnanswered(addingReached.request(calendar.nextBusinessDay));
      inFlight(w, tasksSub);
      return { adding, sent };
    },
    then: ({ adding, sent }) => [
      // The key that the screen created is observed: Then names it through the request.
      requested(adding, [request(todo.addTask, { taskId: sent.input.taskId, title: "Buy eggs" })]),
    ],
  },
);

export const completeAddedTask = scenario(
  "Add a task on the list screen, and press complete on the added task once the list screen shows it; the screen sends completeTask with the key that the screen created for addTask",
  {
    given: milk,
    when: (w) => {
      const { list, tasksSub } = openList(w);
      const adding = w.user.operate(list, "add", { title: "Buy eggs" });
      const { req: sent, reached: addingReached } = replyEmitting(w, adding, todo.addTask, accepted);
      w.peer.calendar.leaveUnanswered(addingReached.request(calendar.nextBusinessDay));
      const eggs = { taskId: sent.input.taskId, title: "Buy eggs", dueAt: null, completedAt: null };
      w.peer.todo.answer(tasksSub, fulfilled({ tasks: [milkRow, eggs] }));
      const completing = w.user.operate(list, "complete", { taskId: sent.input.taskId });
      replyEmitting(w, completing, todo.completeTask, accepted);
      inFlight(w, tasksSub);
      return { completing, sent };
    },
    then: ({ completing, sent }) => [
      requested(completing, [request(todo.completeTask, { taskId: sent.input.taskId })]),
    ],
  },
);

export const completeFromList = scenario(
  "Press complete on an open task in the list screen; the screen sends completeTask",
  {
    given: milk,
    when: (w) => {
      const { list, tasksSub } = openList(w);
      const completing = w.user.operate(list, "complete", { taskId: "task-1" });
      replyEmitting(w, completing, todo.completeTask, accepted);
      inFlight(w, tasksSub);
      return { completing };
    },
    then: ({ completing }) => [requested(completing, [request(todo.completeTask, { taskId: "task-1" })])],
  },
);

export const ignoresListOperationsWhileCompleting = scenario(
  "Operate the list screen while completeTask waits for its answer; the screen offers no complete, reopen, or openTask on any task, no add, and no remindersToggle, and offers them again after the answer",
  {
    given: milkAndCompletedEggs,
    when: (w) => {
      const { list, tasksSub } = openList(w);
      const filtering = w.user.operate(list, "filter", { filter: "all" });
      const { req: allSub } = reply(w, filtering, todo.tasks, fulfilled({ tasks: [completedEggsRow, milkRow] }));
      const completing = w.user.operate(list, "complete", { taskId: "task-1" });
      const busy = w.user.look(list);
      replyEmitting(w, completing, todo.completeTask, accepted);
      const reopening = w.user.operate(list, "reopen", { taskId: "task-2" });
      replyEmitting(w, reopening, todo.reopenTask, accepted);
      inFlight(w, tasksSub, allSub);
      return { busy, reopening };
    },
    then: ({ busy, reopening }) => [
      notOffered(busy, "complete", { taskId: "task-1" }),
      notOffered(busy, "reopen", { taskId: "task-2" }),
      notOffered(busy, "openTask", { taskId: "task-2", title: "Buy eggs" }),
      notOffered(busy, "add", { title: "Buy bread" }),
      notOffered(busy, "remindersToggle", { shouldRemind: false }),
      requested(reopening, [request(todo.reopenTask, { taskId: "task-2" })]),
    ],
  },
);

export const reopenFromList = scenario(
  "Choose the completed filter on the list screen, and press reopen on a completed task; the screen sends reopenTask",
  {
    given: milk,
    when: (w) => {
      const { list, tasksSub } = openList(w);
      const completing = w.client.send(todo.completeTask, { taskId: "task-1" });
      // todo's taskCompleted, the result of the client's completeTask, is still in flight.
      w.net.inFlight(completing.event(todo.taskCompleted));
      const filtering = w.user.operate(list, "filter", { filter: "completed" });
      const { req: completedSub } = reply(w, filtering, todo.tasks, fulfilled({ tasks: [completedMilkRow] }));
      const reopening = w.user.operate(list, "reopen", { taskId: "task-1" });
      replyEmitting(w, reopening, todo.reopenTask, accepted);
      inFlight(w, tasksSub, completedSub);
      return { reopening };
    },
    then: ({ reopening }) => [requested(reopening, [request(todo.reopenTask, { taskId: "task-1" })])],
  },
);

export const offersCompletionOnList = scenario(
  "Look at the list screen; the screen offers complete only on an open task and reopen only on a completed task",
  {
    given: milkAndCompletedEggs,
    when: (w) => {
      const { list, tasksSub } = openList(w);
      const filtering = w.user.operate(list, "filter", { filter: "all" });
      reply(w, filtering, todo.tasks, fulfilled({ tasks: [completedEggsRow, milkRow] }));
      const look = w.user.look(list);
      inFlight(w, tasksSub);
      return { look };
    },
    then: ({ look }) => [
      offered(look, "complete", { taskId: "task-1" }),
      notOffered(look, "reopen", { taskId: "task-1" }),
      offered(look, "reopen", { taskId: "task-2" }),
      notOffered(look, "complete", { taskId: "task-2" }),
    ],
  },
);

export const keepsFilter = scenario(
  "Choose a filter, and open and close the detail screen; the list screen keeps the filter chosen before",
  {
    given: milk,
    when: (w) => {
      const { list, tasksSub } = openList(w);
      const filtering = w.user.operate(list, "filter", { filter: "all" });
      reply(w, filtering, todo.tasks, fulfilled({ tasks: [milkRow] }));
      const { detail, detailSub } = openTask(w, list);
      const closing = w.user.operate(detail, "close");
      inFlight(w, tasksSub, detailSub);
      return { closing, detailSub };
    },
    // Closing ends only the detail subscription; the list does not subscribe again with the open filter.
    then: ({ closing, detailSub }) => [requested(closing, [endOf(detailSub)])],
  },
);

export const completeAndReopenFromDetail = scenario(
  "Press complete on the detail screen, and press reopen while the screen stays open; the screen sends completeTask, then reopenTask",
  {
    given: milk,
    when: (w) => {
      const { detail, detailSub, tasksSub } = openDetail(w);
      const completing = w.user.operate(detail, "complete");
      replyEmitting(w, completing, todo.completeTask, accepted);
      w.peer.todo.answer(detailSub, fulfilled({ task: { ...milkDetail, isCompleted: true } }));
      const reopening = w.user.operate(detail, "reopen");
      replyEmitting(w, reopening, todo.reopenTask, accepted);
      inFlight(w, tasksSub, detailSub);
      return { completing, reopening };
    },
    then: ({ completing, reopening }) => [
      requested(completing, [request(todo.completeTask, { taskId: "task-1" })]),
      requested(reopening, [request(todo.reopenTask, { taskId: "task-1" })]),
    ],
  },
);

export const completedTaskNotCompleted = scenario(
  "Open a completed task on the detail screen; the screen offers no complete",
  {
    given: milk,
    when: (w) => {
      const { list, tasksSub } = openList(w);
      const completing = w.client.send(todo.completeTask, { taskId: "task-1" });
      // todo's taskCompleted, the result of the client's completeTask, is still in flight.
      w.net.inFlight(completing.event(todo.taskCompleted));
      const { detail, detailSub } = openTask(w, list);
      delivered(w, detailSub, fulfilled({ task: { ...milkDetail, isCompleted: true } }));
      const look = w.user.look(detail);
      inFlight(w, tasksSub);
      return { look };
    },
    then: ({ look }) => [notOffered(look, "complete")],
  },
);

export const renameFromDetail = scenario(
  "Finish editing the title field on the detail screen; the screen sends renameTask only if the title changed",
  {
    given: milk,
    when: (w) => {
      const { detail, detailSub, tasksSub } = openDetail(w);
      const same = w.user.operate(detail, "rename", { title: "Buy milk" });
      const changed = w.user.operate(detail, "rename", { title: "Buy soy milk" });
      reply(w, changed, todo.renameTask, accepted);
      inFlight(w, tasksSub, detailSub);
      return { same, changed };
    },
    then: ({ same, changed }) => [
      requested(same, []),
      requested(changed, [request(todo.renameTask, { taskId: "task-1", title: "Buy soy milk" })]),
    ],
  },
);

export const keepsOpenWhileRenaming = scenario(
  "Look at the detail screen while renameTask waits for its answer; the screen offers neither delete nor close, and closes after the answer",
  {
    given: milk,
    when: (w) => {
      const { detail, detailSub, tasksSub } = openDetail(w);
      const renaming = w.user.operate(detail, "rename", { title: "Buy soy milk" });
      const busy = w.user.look(detail);
      reply(w, renaming, todo.renameTask, accepted);
      const closing = w.user.operate(detail, "close");
      inFlight(w, tasksSub, detailSub);
      return { busy, closing, detailSub };
    },
    then: ({ busy, closing, detailSub }) => [
      notOffered(busy, "delete"),
      notOffered(busy, "close"),
      requested(closing, [endOf(detailSub)]),
    ],
  },
);

export const changeDueFromDetail = scenario(
  "Choose due dates on the detail screen before and after opening the due row; the screen offers no dueChoose until the due row opens, sends changeDue only for a time later than now, offers no operation on the due row and no close while changeDue waits for its answer, and collapses the due row after the answer",
  {
    given: milk,
    when: (w) => {
      const { detail, detailSub, tasksSub } = openDetail(w);
      const collapsed = w.user.look(detail);
      w.user.operate(detail, "dueToggle");
      const past = w.user.operate(detail, "dueChoose", { dueAt: "2026-10-24T18:00:00+09:00" });
      const future = w.user.operate(detail, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" });
      const busy = w.user.look(detail);
      reply(w, future, todo.changeDue, accepted);
      const after = w.user.look(detail);
      inFlight(w, tasksSub, detailSub);
      return { collapsed, past, future, busy, after };
    },
    then: ({ collapsed, past, future, busy, after }) => [
      notOffered(collapsed, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" }),
      requested(past, []),
      requested(future, [request(todo.changeDue, { taskId: "task-1", dueAt: "2026-10-27T18:00:00+09:00" })]),
      notOffered(busy, "dueToggle"),
      notOffered(busy, "close"),
      notOffered(after, "dueClear"),
    ],
  },
);

export const clearDueFromDetail = scenario(
  "Open and collapse the due row on the detail screen without choosing a time, then press dueClear; the screen sends no changeDue on collapse, and changeDue with dueAt null on dueClear",
  {
    given: milk,
    when: (w) => {
      const { detail, detailSub, tasksSub } = openDetail(w);
      w.user.operate(detail, "dueToggle");
      const collapse = w.user.operate(detail, "dueToggle");
      w.user.operate(detail, "dueToggle");
      const clearing = w.user.operate(detail, "dueClear");
      const { reached: clearingReached } = reply(w, clearing, todo.changeDue, accepted);
      w.peer.calendar.leaveUnanswered(clearingReached.request(calendar.nextBusinessDay));
      inFlight(w, tasksSub, detailSub);
      return { collapse, clearing };
    },
    then: ({ collapse, clearing }) => [
      requested(collapse, []),
      requested(clearing, [request(todo.changeDue, { taskId: "task-1", dueAt: null })]),
    ],
  },
);

export const keepsSameDue = scenario(
  "Choose the task's current due date on the detail screen; the screen collapses the due row without sending changeDue",
  {
    given: milk,
    when: (w) => {
      const { detail } = openDetail(w);
      w.user.operate(detail, "dueToggle");
      const same = w.user.operate(detail, "dueChoose", { dueAt: "2026-10-26T18:00:00+09:00" });
      const look = w.user.look(detail);
      return { same, look };
    },
    then: ({ same, look }) => [
      requested(same, []),
      notOffered(look, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" }),
    ],
  },
);

export const clearsOnlyDue = scenario(
  "Open a task without a due date on the detail screen; the screen offers no dueClear",
  {
    given: milk,
    when: (w) => {
      const { list, tasksSub } = openList(w);
      const clear = w.client.send(todo.changeDue, { taskId: "task-1", dueAt: null });
      w.peer.calendar.leaveUnanswered(clear.request(calendar.nextBusinessDay));
      const { detail, detailSub } = openTask(w, list);
      delivered(w, detailSub, fulfilled({ task: { ...milkDetail, dueAt: null, remindAt: null } }));
      w.user.operate(detail, "dueToggle");
      const look = w.user.look(detail);
      inFlight(w, tasksSub);
      return { look };
    },
    then: ({ look }) => [notOffered(look, "dueClear")],
  },
);

export const completeWhileDueExpanded = scenario(
  "Press complete while the due row is open on the detail screen; the screen sends completeTask and keeps the due row open",
  {
    given: milk,
    when: (w) => {
      const { detail, detailSub, tasksSub } = openDetail(w);
      w.user.operate(detail, "dueToggle");
      const completing = w.user.operate(detail, "complete");
      replyEmitting(w, completing, todo.completeTask, accepted);
      const clearing = w.user.operate(detail, "dueClear");
      const { reached: clearingReached } = reply(w, clearing, todo.changeDue, accepted);
      w.peer.calendar.leaveUnanswered(clearingReached.request(calendar.nextBusinessDay));
      inFlight(w, tasksSub, detailSub);
      return { clearing };
    },
    then: ({ clearing }) => [requested(clearing, [request(todo.changeDue, { taskId: "task-1", dueAt: null })])],
  },
);

export const deleteFromDetail = scenario(
  "Press delete on the detail screen; the screen sends deleteTask without asking the user, offers no edit and no close while deleteTask waits for its answer",
  {
    given: milk,
    when: (w) => {
      const { detail, detailSub, tasksSub } = openDetail(w);
      const deleting = w.user.operate(detail, "delete");
      const busy = w.user.look(detail);
      const { req: deleteReq } = reply(w, deleting, todo.deleteTask, accepted);
      // todo's taskDeleted, the result of deleteReq, is still in flight.
      inFlight(w, tasksSub, detailSub, deleteReq);
      return { deleting, busy, detailSub };
    },
    then: ({ deleting, busy, detailSub }) => [
      requested(deleting, [request(todo.deleteTask, { taskId: "task-1" }), endOf(detailSub)]),
      notOffered(busy, "rename", { title: "Buy soy milk" }),
      notOffered(busy, "complete"),
      notOffered(busy, "close"),
    ],
  },
);

export const closesDeletedTask = scenario("Receive taskDeleted for the task on the detail screen; the screen closes", {
  given: milk,
  when: (w) => {
    const { list, tasksSub } = openList(w);
    const { detailSub } = openTask(w, list);
    const del = w.client.send(todo.deleteTask, { taskId: "task-1" });
    const deleted = w.peer.todo.emit(todo.taskDeleted, { taskId: "task-1" }, { resultOf: del });
    inFlight(w, tasksSub, detailSub);
    return { deleted, detailSub };
  },
  then: ({ deleted, detailSub }) => [requested(deleted, [endOf(detailSub)])],
});

export const changesReminders = scenario(
  "Press remindersToggle on the list screen; the screen sends changeReminders and accepts user operations again after the answer",
  {
    given: milk,
    when: (w) => {
      const { list, tasksSub, settingsSub } = openList(w);
      const toggling = w.user.operate(list, "remindersToggle", { shouldRemind: false });
      reply(w, toggling, todo.changeReminders, accepted);
      const filtering = w.user.operate(list, "filter", { filter: "all" });
      inFlight(w, settingsSub, tasksSub, filtering.request(todo.tasks));
      return { toggling, filtering, tasksSub };
    },
    then: ({ toggling, filtering, tasksSub }) => [
      requested(toggling, [request(todo.changeReminders, { shouldRemind: false })]),
      // Accepted again: the filter operation changes the subscription.
      requested(filtering, [endOf(tasksSub), subscription(todo.tasks, { filter: "all" })]),
    ],
  },
);

export const ignoresListOperationsWhileSending = scenario(
  "Look at the list screen while addTask and changeReminders wait for their answers; the screen offers no add, remindersToggle, or openTask",
  {
    given: milk,
    when: (w) => {
      const { list, tasksSub, settingsSub } = openList(w);
      const adding = w.user.operate(list, "add", { title: "Buy eggs" });
      const whileAdding = w.user.look(list);
      const { reached: addingReached } = replyEmitting(w, adding, todo.addTask, accepted);
      w.peer.calendar.leaveUnanswered(addingReached.request(calendar.nextBusinessDay));
      const toggling = w.user.operate(list, "remindersToggle", { shouldRemind: false });
      const whileToggling = w.user.look(list);
      reply(w, toggling, todo.changeReminders, accepted);
      inFlight(w, tasksSub, settingsSub);
      return { whileAdding, whileToggling };
    },
    then: ({ whileAdding, whileToggling }) =>
      [whileAdding, whileToggling].flatMap((look) => [
        notOffered(look, "add", { title: "Buy bread" }),
        notOffered(look, "remindersToggle", { shouldRemind: false }),
        notOffered(look, "openTask", { taskId: "task-1", title: "Buy milk" }),
      ]),
  },
);

export const retriesAfterListRejections = scenario(
  "Let todo reject addTask and changeReminders; the list screen accepts add and remindersToggle again",
  {
    given: milk,
    when: (w) => {
      const { list, tasksSub, settingsSub } = openList(w);
      const add1 = w.user.operate(list, "add", { title: "Buy eggs" });
      unreachable(w, add1, todo.addTask);
      const add2 = w.user.operate(list, "add", { title: "Buy eggs" });
      const { reached: add2Reached } = replyEmitting(w, add2, todo.addTask, accepted);
      w.peer.calendar.leaveUnanswered(add2Reached.request(calendar.nextBusinessDay));
      const toggle1 = w.user.operate(list, "remindersToggle", { shouldRemind: false });
      unreachable(w, toggle1, todo.changeReminders);
      const toggle2 = w.user.operate(list, "remindersToggle", { shouldRemind: false });
      reply(w, toggle2, todo.changeReminders, accepted);
      inFlight(w, tasksSub, settingsSub);
      return { add2, toggle2 };
    },
    then: ({ add2, toggle2 }) => [
      requested(add2, [request(todo.addTask, { taskId: add2.request(todo.addTask).input.taskId, title: "Buy eggs" })]),
      requested(toggle2, [request(todo.changeReminders, { shouldRemind: false })]),
    ],
  },
);

export const retriesAfterRowRejections = scenario(
  "Let todo reject completeTask and reopenTask; the list screen accepts complete and reopen on the same task again",
  {
    given: milkAndCompletedEggs,
    when: (w) => {
      const { list, tasksSub } = openList(w);
      const filtering = w.user.operate(list, "filter", { filter: "all" });
      const { req: allSub } = reply(w, filtering, todo.tasks, fulfilled({ tasks: [completedEggsRow, milkRow] }));
      const complete1 = w.user.operate(list, "complete", { taskId: "task-1" });
      unreachable(w, complete1, todo.completeTask);
      const complete2 = w.user.operate(list, "complete", { taskId: "task-1" });
      replyEmitting(w, complete2, todo.completeTask, accepted);
      const reopen1 = w.user.operate(list, "reopen", { taskId: "task-2" });
      unreachable(w, reopen1, todo.reopenTask);
      const reopen2 = w.user.operate(list, "reopen", { taskId: "task-2" });
      replyEmitting(w, reopen2, todo.reopenTask, accepted);
      inFlight(w, tasksSub, allSub);
      return { complete2, reopen2 };
    },
    then: ({ complete2, reopen2 }) => [
      requested(complete2, [request(todo.completeTask, { taskId: "task-1" })]),
      requested(reopen2, [request(todo.reopenTask, { taskId: "task-2" })]),
    ],
  },
);

export const retriesAfterRenameAndDueRejections = scenario(
  "Let todo reject renameTask and changeDue; the detail screen accepts rename and due date changes again",
  {
    given: milk,
    when: (w) => {
      const { detail, detailSub, tasksSub } = openDetail(w);
      const rename1 = w.user.operate(detail, "rename", { title: "Buy soy milk" });
      unreachable(w, rename1, todo.renameTask);
      const rename2 = w.user.operate(detail, "rename", { title: "Buy soy milk" });
      reply(w, rename2, todo.renameTask, accepted);
      w.user.operate(detail, "dueToggle");
      const due1 = w.user.operate(detail, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" });
      unreachable(w, due1, todo.changeDue);
      w.user.operate(detail, "dueToggle");
      const due2 = w.user.operate(detail, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" });
      reply(w, due2, todo.changeDue, accepted);
      inFlight(w, tasksSub, detailSub);
      return { rename2, due2 };
    },
    then: ({ rename2, due2 }) => [
      requested(rename2, [request(todo.renameTask, { taskId: "task-1", title: "Buy soy milk" })]),
      requested(due2, [request(todo.changeDue, { taskId: "task-1", dueAt: "2026-10-27T18:00:00+09:00" })]),
    ],
  },
);

export const retriesAfterCompletionRejections = scenario(
  "Look at the detail screen while completeTask waits for its answer, and let todo reject completeTask and reopenTask; the screen offers neither complete nor close while waiting, and accepts complete and reopen again after each rejection",
  {
    given: milk,
    when: (w) => {
      const { detail, detailSub, tasksSub } = openDetail(w);
      const complete1 = w.user.operate(detail, "complete");
      const busy = w.user.look(detail);
      unreachable(w, complete1, todo.completeTask);
      const complete2 = w.user.operate(detail, "complete");
      replyEmitting(w, complete2, todo.completeTask, accepted);
      w.peer.todo.answer(detailSub, fulfilled({ task: { ...milkDetail, isCompleted: true } }));
      const reopen1 = w.user.operate(detail, "reopen");
      unreachable(w, reopen1, todo.reopenTask);
      const reopen2 = w.user.operate(detail, "reopen");
      replyEmitting(w, reopen2, todo.reopenTask, accepted);
      inFlight(w, tasksSub, detailSub);
      return { busy, complete2, reopen2 };
    },
    then: ({ busy, complete2, reopen2 }) => [
      notOffered(busy, "complete"),
      notOffered(busy, "close"),
      requested(complete2, [request(todo.completeTask, { taskId: "task-1" })]),
      requested(reopen2, [request(todo.reopenTask, { taskId: "task-1" })]),
    ],
  },
);

export const keepsEditingAfterDeleteRejected = scenario(
  "Let todo reject deleteTask; the detail screen stays open and accepts operations again",
  {
    given: milk,
    when: (w) => {
      const { detail, detailSub, tasksSub } = openDetail(w);
      const deleting = w.user.operate(detail, "delete");
      const rejected = unreachable(w, deleting, todo.deleteTask);
      // The screen subscribes again after the rejection.
      const resubscribed = rejected.request(todo.taskDetail);
      delivered(w, resubscribed, fulfilled({ task: milkDetail }));
      const completing = w.user.operate(detail, "complete");
      replyEmitting(w, completing, todo.completeTask, accepted);
      inFlight(w, tasksSub, detailSub, resubscribed);
      return { completing };
    },
    then: ({ completing }) => [requested(completing, [request(todo.completeTask, { taskId: "task-1" })])],
  },
);

export const keepsDetailWhenOtherTaskDeleted = scenario(
  "Receive taskDeleted for another task while the detail screen is open; the screen stays open",
  {
    given: milkAndCompletedEggs,
    when: (w) => {
      const { detail, detailSub, tasksSub } = openDetail(w);
      const del = w.client.send(todo.deleteTask, { taskId: "task-2" });
      const deleted = w.peer.todo.emit(todo.taskDeleted, { taskId: "task-2" }, { resultOf: del });
      const completing = w.user.operate(detail, "complete");
      replyEmitting(w, completing, todo.completeTask, accepted);
      inFlight(w, tasksSub, detailSub);
      return { deleted, completing };
    },
    then: ({ deleted, completing }) => [
      requested(deleted, []),
      requested(completing, [request(todo.completeTask, { taskId: "task-1" })]),
    ],
  },
);

export const openTaskNotReopened = scenario("Open an open task on the detail screen; the screen offers no reopen", {
  given: milk,
  when: (w) => {
    const { detail } = openDetail(w);
    const look = w.user.look(detail);
    return { look };
  },
  then: ({ look }) => [notOffered(look, "reopen")],
});
