import {
  accepted,
  endOf,
  external,
  fulfilled,
  notOffered,
  type OutputOf,
  offered,
  requested,
  requestOf,
  run,
  type ScreenRef,
  subscriptionOf,
} from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./data.ts";
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
  given({
    start: "2026-10-25T10:00:00+09:00",
    records: {},
    peers: [
      run(todo, { Task, Settings: { shouldRemind: true } }),
      // todo's run asks calendar when a task's reminder becomes pending.
      external(calendar),
    ],
  });
const milk = givenTasks([milkRecord]);
const milkAndCompletedEggs = givenTasks([milkRecord, completedEggsRecord]);

const milkRow = { taskId: "task-1", title: "Buy milk", dueAt: "2026-10-26T18:00:00+09:00", completedAt: null };
const completedMilkRow = { ...milkRow, completedAt: "2026-10-25T10:00:00+09:00" };
const completedEggsRow = {
  taskId: "task-2",
  title: "Buy eggs",
  dueAt: null,
  completedAt: "2026-10-25T09:00:00+09:00",
};
const milkDetail = {
  title: "Buy milk",
  isCompleted: false,
  dueAt: "2026-10-26T18:00:00+09:00",
  createdAt: "2026-10-25T08:00:00+09:00",
  remindAt: "2026-10-26T18:00:00+09:00",
};

const openList = milk.step((w, tasks: OutputOf<typeof todo.tasks>["tasks"] = [milkRow]) => {
  const list = w.startup.screen(taskListScreen);
  const tasksSub = w.startup.subscription(todo.tasks);
  const tasksReached = w.net.deliver(tasksSub);
  w.net.deliver(w.peer.todo.answer(tasksSub, fulfilled({ tasks })));
  const settingsSub = w.startup.subscription(todo.reminderSettings);
  const settingsReached = w.net.deliver(settingsSub);
  w.net.deliver(w.peer.todo.answer(settingsSub, fulfilled({ shouldRemind: true })));
  return { list, tasksSub, tasksReached, settingsSub, settingsReached };
});

const openTask = milk.step((w, list: ScreenRef<typeof taskListScreen>) => {
  const opening = w.user.operate(list, "openTask", { taskId: "task-1", title: "Buy milk" });
  const detail = opening.screen(taskDetailScreen);
  return { detail, detailSub: opening.subscription(todo.taskDetail) };
});

const openDetail = milk.step((w) => {
  const opened = openList(w);
  const { detail, detailSub } = openTask(w, opened.list);
  const detailReached = w.net.deliver(detailSub);
  w.net.deliver(w.peer.todo.answer(detailSub, fulfilled({ task: milkDetail })));
  return { ...opened, detail, detailSub, detailReached };
});

export const addTask = scenario({
  description: "Enter a title in the new task field of the list screen and press add; the screen sends addTask",
  given: milk,
  when: (w) => {
    const { list, tasksReached } = openList(w);
    const adding = w.user.operate(list, "add", { title: "Buy eggs" });
    const sent = adding.request(todo.addTask);
    const addingReached = w.net.deliver(sent);
    w.net.deliver(w.peer.todo.answer(sent, accepted));
    w.net.deliver(addingReached.request(calendar.nextBusinessDay));
    w.peer.calendar.leaveUnanswered(addingReached.request(calendar.nextBusinessDay));
    w.net.leaveInFlight(addingReached.event(todo.taskAdded));
    w.net.leaveInFlight(addingReached.answer(tasksReached));
    return { adding, sent };
  },
  then: ({ adding, sent }) => [
    // The key that the screen created is observed: Then names it through the request.
    requested(adding, [requestOf(todo.addTask, { taskId: sent.input.taskId, title: "Buy eggs" })]),
  ],
});

export const completeAddedTask = scenario({
  description:
    "Add a task on the list screen, and press complete on the added task once the list screen shows it; the screen sends completeTask with the key that the screen created for addTask",
  given: milk,
  when: (w) => {
    const { list, tasksSub, tasksReached } = openList(w);
    const adding = w.user.operate(list, "add", { title: "Buy eggs" });
    const sent = adding.request(todo.addTask);
    const addingReached = w.net.deliver(sent);
    w.net.deliver(w.peer.todo.answer(sent, accepted));
    w.net.deliver(addingReached.request(calendar.nextBusinessDay));
    w.peer.calendar.leaveUnanswered(addingReached.request(calendar.nextBusinessDay));
    const eggs = { taskId: sent.input.taskId, title: "Buy eggs", dueAt: null, completedAt: null };
    w.net.deliver(w.peer.todo.answer(tasksSub, fulfilled({ tasks: [milkRow, eggs] })));
    const completing = w.user.operate(list, "complete", { taskId: sent.input.taskId });
    const completingReached = w.net.deliver(completing.request(todo.completeTask));
    w.net.deliver(w.peer.todo.answer(completing.request(todo.completeTask), accepted));
    w.net.leaveInFlight(addingReached.event(todo.taskAdded));
    w.net.leaveInFlight(completingReached.event(todo.taskCompleted));
    w.net.leaveInFlight(completingReached.answer(tasksReached));
    return { completing, sent };
  },
  then: ({ completing, sent }) => [
    requested(completing, [requestOf(todo.completeTask, { taskId: sent.input.taskId })]),
  ],
});

export const completeFromList = scenario({
  description: "Press complete on an open task in the list screen; the screen sends completeTask",
  given: milk,
  when: (w) => {
    const { list, tasksReached } = openList(w);
    const completing = w.user.operate(list, "complete", { taskId: "task-1" });
    const completingReached = w.net.deliver(completing.request(todo.completeTask));
    w.net.deliver(w.peer.todo.answer(completing.request(todo.completeTask), accepted));
    w.net.leaveInFlight(completingReached.event(todo.taskCompleted));
    w.net.leaveInFlight(completingReached.answer(tasksReached));
    return { completing };
  },
  then: ({ completing }) => [requested(completing, [requestOf(todo.completeTask, { taskId: "task-1" })])],
});

export const ignoresListOperationsWhileCompleting = scenario({
  description:
    "Operate the list screen while completeTask waits for its answer; the screen offers no complete, reopen, or openTask on any task, no add, and no remindersToggle, and offers them again after the answer",
  given: milkAndCompletedEggs,
  when: (w) => {
    const { list, tasksSub, tasksReached } = openList(w);
    const filtering = w.user.operate(list, "filter", { filter: "all" });
    const allSub = filtering.subscription(todo.tasks);
    const allReached = w.net.deliver(allSub);
    w.net.deliver(w.peer.todo.answer(allSub, fulfilled({ tasks: [completedEggsRow, milkRow] })));
    const completing = w.user.operate(list, "complete", { taskId: "task-1" });
    const busy = w.user.look(list);
    const completingReached = w.net.deliver(completing.request(todo.completeTask));
    w.net.deliver(w.peer.todo.answer(completing.request(todo.completeTask), accepted));
    const reopening = w.user.operate(list, "reopen", { taskId: "task-2" });
    const reopeningReached = w.net.deliver(reopening.request(todo.reopenTask));
    w.net.deliver(w.peer.todo.answer(reopening.request(todo.reopenTask), accepted));
    w.net.leaveInFlight(filtering.end(tasksSub));
    w.net.leaveInFlight(completingReached.event(todo.taskCompleted));
    w.net.leaveInFlight(completingReached.answer(tasksReached));
    w.net.leaveInFlight(completingReached.answer(allReached));
    w.net.leaveInFlight(reopeningReached.event(todo.taskReopened));
    w.net.leaveInFlight(reopeningReached.answer(tasksReached));
    w.net.leaveInFlight(reopeningReached.answer(allReached));
    return { busy, reopening };
  },
  then: ({ busy, reopening }) => [
    notOffered(busy, "complete", { taskId: "task-1" }),
    notOffered(busy, "reopen", { taskId: "task-2" }),
    notOffered(busy, "openTask", { taskId: "task-2", title: "Buy eggs" }),
    notOffered(busy, "add", { title: "Buy bread" }),
    notOffered(busy, "remindersToggle", { shouldRemind: false }),
    requested(reopening, [requestOf(todo.reopenTask, { taskId: "task-2" })]),
  ],
});

export const reopenFromList = scenario({
  description:
    "Choose the completed filter on the list screen, and press reopen on a completed task; the screen sends reopenTask",
  given: milk,
  when: (w) => {
    const { list, tasksSub, tasksReached } = openList(w);
    const completing = w.client.send(todo.completeTask, { taskId: "task-1" });
    w.net.leaveInFlight(completing.event(todo.taskCompleted));
    const filtering = w.user.operate(list, "filter", { filter: "completed" });
    const completedSub = filtering.subscription(todo.tasks);
    const completedReached = w.net.deliver(completedSub);
    w.net.deliver(w.peer.todo.answer(completedSub, fulfilled({ tasks: [completedMilkRow] })));
    const reopening = w.user.operate(list, "reopen", { taskId: "task-1" });
    const reopeningReached = w.net.deliver(reopening.request(todo.reopenTask));
    w.net.deliver(w.peer.todo.answer(reopening.request(todo.reopenTask), accepted));
    w.net.leaveInFlight(completing.answer(tasksReached));
    w.net.leaveInFlight(filtering.end(tasksSub));
    w.net.leaveInFlight(reopeningReached.event(todo.taskReopened));
    w.net.leaveInFlight(reopeningReached.answer(tasksReached));
    w.net.leaveInFlight(reopeningReached.answer(completedReached));
    return { reopening };
  },
  then: ({ reopening }) => [requested(reopening, [requestOf(todo.reopenTask, { taskId: "task-1" })])],
});

export const offersCompletionOnList = scenario({
  description:
    "Look at the list screen; the screen offers complete only on an open task and reopen only on a completed task",
  given: milkAndCompletedEggs,
  when: (w) => {
    const { list, tasksSub } = openList(w);
    const filtering = w.user.operate(list, "filter", { filter: "all" });
    w.net.deliver(filtering.subscription(todo.tasks));
    w.net.deliver(
      w.peer.todo.answer(filtering.subscription(todo.tasks), fulfilled({ tasks: [completedEggsRow, milkRow] })),
    );
    const look = w.user.look(list);
    w.net.leaveInFlight(filtering.end(tasksSub));
    return { look };
  },
  then: ({ look }) => [
    offered(look, "complete", { taskId: "task-1" }),
    notOffered(look, "reopen", { taskId: "task-1" }),
    offered(look, "reopen", { taskId: "task-2" }),
    notOffered(look, "complete", { taskId: "task-2" }),
  ],
});

export const keepsFilter = scenario({
  description: "Choose a filter, and open and close the detail screen; the list screen keeps the filter chosen before",
  given: milk,
  when: (w) => {
    const { list, tasksSub } = openList(w);
    const filtering = w.user.operate(list, "filter", { filter: "all" });
    w.net.deliver(filtering.subscription(todo.tasks));
    w.net.deliver(w.peer.todo.answer(filtering.subscription(todo.tasks), fulfilled({ tasks: [milkRow] })));
    const { detail, detailSub } = openTask(w, list);
    const closing = w.user.operate(detail, "close");
    w.net.leaveInFlight(filtering.end(tasksSub));
    w.net.leaveInFlight(detailSub);
    w.net.leaveInFlight(closing.end(detailSub));
    return { closing, detailSub };
  },
  // Closing ends only the detail subscription; the list does not subscribe again with the open filter.
  then: ({ closing, detailSub }) => [requested(closing, [endOf(detailSub)])],
});

export const completeAndReopenFromDetail = scenario({
  description:
    "Press complete on the detail screen, and press reopen while the screen stays open; the screen sends completeTask, then reopenTask",
  given: milk,
  when: (w) => {
    const { tasksReached, detail, detailSub, detailReached } = openDetail(w);
    const completing = w.user.operate(detail, "complete");
    const completingReached = w.net.deliver(completing.request(todo.completeTask));
    w.net.deliver(w.peer.todo.answer(completing.request(todo.completeTask), accepted));
    w.net.deliver(w.peer.todo.answer(detailSub, fulfilled({ task: { ...milkDetail, isCompleted: true } })));
    const reopening = w.user.operate(detail, "reopen");
    const reopeningReached = w.net.deliver(reopening.request(todo.reopenTask));
    w.net.deliver(w.peer.todo.answer(reopening.request(todo.reopenTask), accepted));
    w.net.leaveInFlight(completingReached.event(todo.taskCompleted));
    w.net.leaveInFlight(completingReached.answer(tasksReached));
    w.net.leaveInFlight(reopeningReached.event(todo.taskReopened));
    w.net.leaveInFlight(reopeningReached.answer(tasksReached));
    w.net.leaveInFlight(reopeningReached.answer(detailReached));
    return { completing, reopening };
  },
  then: ({ completing, reopening }) => [
    requested(completing, [requestOf(todo.completeTask, { taskId: "task-1" })]),
    requested(reopening, [requestOf(todo.reopenTask, { taskId: "task-1" })]),
  ],
});

export const completedTaskNotCompleted = scenario({
  description: "Open a completed task on the detail screen; the screen offers no complete",
  given: milk,
  when: (w) => {
    const { list, tasksReached } = openList(w);
    const completing = w.client.send(todo.completeTask, { taskId: "task-1" });
    w.net.leaveInFlight(completing.event(todo.taskCompleted));
    const { detail, detailSub } = openTask(w, list);
    w.net.deliver(detailSub);
    w.net.deliver(w.peer.todo.answer(detailSub, fulfilled({ task: { ...milkDetail, isCompleted: true } })));
    const look = w.user.look(detail);
    w.net.leaveInFlight(completing.answer(tasksReached));
    return { look };
  },
  then: ({ look }) => [notOffered(look, "complete")],
});

export const renameFromDetail = scenario({
  description:
    "Finish editing the title field on the detail screen; the screen sends renameTask only if the title changed",
  given: milk,
  when: (w) => {
    const { tasksReached, detail, detailReached } = openDetail(w);
    const same = w.user.operate(detail, "rename", { title: "Buy milk" });
    const changed = w.user.operate(detail, "rename", { title: "Buy soy milk" });
    const changedReached = w.net.deliver(changed.request(todo.renameTask));
    w.net.deliver(w.peer.todo.answer(changed.request(todo.renameTask), accepted));
    w.net.leaveInFlight(changedReached.answer(tasksReached));
    w.net.leaveInFlight(changedReached.answer(detailReached));
    return { same, changed };
  },
  then: ({ same, changed }) => [
    requested(same, []),
    requested(changed, [requestOf(todo.renameTask, { taskId: "task-1", title: "Buy soy milk" })]),
  ],
});

export const keepsOpenWhileRenaming = scenario({
  description:
    "Look at the detail screen while renameTask waits for its answer; the screen offers neither delete nor close, and closes after the answer",
  given: milk,
  when: (w) => {
    const { tasksReached, detail, detailSub, detailReached } = openDetail(w);
    const renaming = w.user.operate(detail, "rename", { title: "Buy soy milk" });
    const busy = w.user.look(detail);
    const renamingReached = w.net.deliver(renaming.request(todo.renameTask));
    w.net.deliver(w.peer.todo.answer(renaming.request(todo.renameTask), accepted));
    const closing = w.user.operate(detail, "close");
    w.net.leaveInFlight(renamingReached.answer(tasksReached));
    w.net.leaveInFlight(renamingReached.answer(detailReached));
    w.net.leaveInFlight(closing.end(detailSub));
    return { busy, closing, detailSub };
  },
  then: ({ busy, closing, detailSub }) => [
    notOffered(busy, "delete"),
    notOffered(busy, "close"),
    requested(closing, [endOf(detailSub)]),
  ],
});

export const changeDueFromDetail = scenario({
  description:
    "Choose due dates on the detail screen before and after opening the due row; the screen offers no dueChoose until the due row opens, sends changeDue only for a time later than now, offers no operation on the due row and no close while changeDue waits for its answer, and collapses the due row after the answer",
  given: milk,
  when: (w) => {
    const { tasksReached, detail, detailReached } = openDetail(w);
    const collapsed = w.user.look(detail);
    w.user.operate(detail, "dueToggle");
    const past = w.user.operate(detail, "dueChoose", { dueAt: "2026-10-24T18:00:00+09:00" });
    const future = w.user.operate(detail, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" });
    const busy = w.user.look(detail);
    const futureReached = w.net.deliver(future.request(todo.changeDue));
    w.net.deliver(w.peer.todo.answer(future.request(todo.changeDue), accepted));
    const after = w.user.look(detail);
    w.net.leaveInFlight(futureReached.answer(tasksReached));
    w.net.leaveInFlight(futureReached.answer(detailReached));
    return { collapsed, past, future, busy, after };
  },
  then: ({ collapsed, past, future, busy, after }) => [
    notOffered(collapsed, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" }),
    requested(past, []),
    requested(future, [requestOf(todo.changeDue, { taskId: "task-1", dueAt: "2026-10-27T18:00:00+09:00" })]),
    notOffered(busy, "dueToggle"),
    notOffered(busy, "close"),
    notOffered(after, "dueClear"),
  ],
});

export const clearDueFromDetail = scenario({
  description:
    "Open and collapse the due row on the detail screen without choosing a time, then press dueClear; the screen sends no changeDue on collapse, and changeDue with dueAt null on dueClear",
  given: milk,
  when: (w) => {
    const { tasksReached, detail, detailReached } = openDetail(w);
    w.user.operate(detail, "dueToggle");
    const collapse = w.user.operate(detail, "dueToggle");
    w.user.operate(detail, "dueToggle");
    const clearing = w.user.operate(detail, "dueClear");
    const clearingRequest = clearing.request(todo.changeDue);
    const clearingReached = w.net.deliver(clearingRequest);
    w.net.deliver(w.peer.todo.answer(clearingRequest, accepted));
    w.net.deliver(clearingReached.request(calendar.nextBusinessDay));
    w.peer.calendar.leaveUnanswered(clearingReached.request(calendar.nextBusinessDay));
    w.net.leaveInFlight(clearingReached.answer(tasksReached));
    w.net.leaveInFlight(clearingReached.answer(detailReached));
    return { collapse, clearing };
  },
  then: ({ collapse, clearing }) => [
    requested(collapse, []),
    requested(clearing, [requestOf(todo.changeDue, { taskId: "task-1", dueAt: null })]),
  ],
});

export const keepsSameDue = scenario({
  description:
    "Choose the task's current due date on the detail screen; the screen collapses the due row without sending changeDue",
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
});

export const clearsOnlyDue = scenario({
  description: "Open a task without a due date on the detail screen; the screen offers no dueClear",
  given: milk,
  when: (w) => {
    const { list, tasksReached } = openList(w);
    const clear = w.client.send(todo.changeDue, { taskId: "task-1", dueAt: null });
    w.net.deliver(clear.request(calendar.nextBusinessDay));
    w.peer.calendar.leaveUnanswered(clear.request(calendar.nextBusinessDay));
    const { detail, detailSub } = openTask(w, list);
    w.net.deliver(detailSub);
    w.net.deliver(w.peer.todo.answer(detailSub, fulfilled({ task: { ...milkDetail, dueAt: null, remindAt: null } })));
    w.user.operate(detail, "dueToggle");
    const look = w.user.look(detail);
    w.net.leaveInFlight(clear.answer(tasksReached));
    return { look };
  },
  then: ({ look }) => [notOffered(look, "dueClear")],
});

export const completeWhileDueExpanded = scenario({
  description:
    "Press complete while the due row is open on the detail screen; the screen sends completeTask and keeps the due row open",
  given: milk,
  when: (w) => {
    const { tasksReached, detail, detailReached } = openDetail(w);
    w.user.operate(detail, "dueToggle");
    const completing = w.user.operate(detail, "complete");
    const completingReached = w.net.deliver(completing.request(todo.completeTask));
    w.net.deliver(w.peer.todo.answer(completing.request(todo.completeTask), accepted));
    const clearing = w.user.operate(detail, "dueClear");
    const clearingRequest = clearing.request(todo.changeDue);
    const clearingReached = w.net.deliver(clearingRequest);
    w.net.deliver(w.peer.todo.answer(clearingRequest, accepted));
    w.net.deliver(clearingReached.request(calendar.nextBusinessDay));
    w.peer.calendar.leaveUnanswered(clearingReached.request(calendar.nextBusinessDay));
    w.net.leaveInFlight(completingReached.event(todo.taskCompleted));
    w.net.leaveInFlight(completingReached.answer(tasksReached));
    w.net.leaveInFlight(completingReached.answer(detailReached));
    w.net.leaveInFlight(clearingReached.answer(detailReached));
    return { clearing };
  },
  then: ({ clearing }) => [requested(clearing, [requestOf(todo.changeDue, { taskId: "task-1", dueAt: null })])],
});

export const deleteFromDetail = scenario({
  description:
    "Press delete on the detail screen; the screen sends deleteTask without asking the user, offers no edit and no close while deleteTask waits for its answer",
  given: milk,
  when: (w) => {
    const { tasksReached, detail, detailSub, detailReached } = openDetail(w);
    const deleting = w.user.operate(detail, "delete");
    const busy = w.user.look(detail);
    const deleteReq = deleting.request(todo.deleteTask);
    const deleteReached = w.net.deliver(deleteReq);
    w.net.deliver(w.peer.todo.answer(deleteReq, accepted));
    w.net.leaveInFlight(deleting.end(detailSub));
    w.net.leaveInFlight(deleteReached.event(todo.taskDeleted));
    w.net.leaveInFlight(deleteReached.answer(tasksReached));
    w.net.leaveInFlight(deleteReached.answer(detailReached));
    return { deleting, busy, detailSub };
  },
  then: ({ deleting, busy, detailSub }) => [
    requested(deleting, [requestOf(todo.deleteTask, { taskId: "task-1" }), endOf(detailSub)]),
    notOffered(busy, "rename", { title: "Buy soy milk" }),
    notOffered(busy, "complete"),
    notOffered(busy, "close"),
  ],
});

export const closesDeletedTask = scenario({
  description: "Receive taskDeleted for the task on the detail screen; the screen closes",
  given: milk,
  when: (w) => {
    const { list, tasksReached } = openList(w);
    const { detailSub } = openTask(w, list);
    const del = w.client.send(todo.deleteTask, { taskId: "task-1" });
    const deleted = w.net.deliver(w.peer.todo.emit(todo.taskDeleted, { taskId: "task-1" }, { resultOf: del }));
    w.net.leaveInFlight(detailSub);
    w.net.leaveInFlight(del.answer(tasksReached));
    w.net.leaveInFlight(deleted.end(detailSub));
    return { deleted, detailSub };
  },
  then: ({ deleted, detailSub }) => [requested(deleted, [endOf(detailSub)])],
});

export const changesReminders = scenario({
  description:
    "Press remindersToggle on the list screen; the screen sends changeReminders and accepts user operations again after the answer",
  given: milk,
  when: (w) => {
    const { list, tasksSub, settingsReached } = openList(w);
    const toggling = w.user.operate(list, "remindersToggle", { shouldRemind: false });
    const togglingReached = w.net.deliver(toggling.request(todo.changeReminders));
    w.net.deliver(w.peer.todo.answer(toggling.request(todo.changeReminders), accepted));
    const filtering = w.user.operate(list, "filter", { filter: "all" });
    w.net.leaveInFlight(togglingReached.answer(settingsReached));
    w.net.leaveInFlight(filtering.end(tasksSub));
    w.net.leaveInFlight(filtering.subscription(todo.tasks));
    return { toggling, filtering, tasksSub };
  },
  then: ({ toggling, filtering, tasksSub }) => [
    requested(toggling, [requestOf(todo.changeReminders, { shouldRemind: false })]),
    // Accepted again: the filter operation changes the subscription.
    requested(filtering, [endOf(tasksSub), subscriptionOf(todo.tasks, { filter: "all" })]),
  ],
});

export const ignoresListOperationsWhileSending = scenario({
  description:
    "Look at the list screen while addTask and changeReminders wait for their answers; the screen offers no add, remindersToggle, or openTask",
  given: milk,
  when: (w) => {
    const { list, tasksReached, settingsReached } = openList(w);
    const adding = w.user.operate(list, "add", { title: "Buy eggs" });
    const whileAdding = w.user.look(list);
    const addingRequest = adding.request(todo.addTask);
    const addingReached = w.net.deliver(addingRequest);
    w.net.deliver(w.peer.todo.answer(addingRequest, accepted));
    w.net.deliver(addingReached.request(calendar.nextBusinessDay));
    w.peer.calendar.leaveUnanswered(addingReached.request(calendar.nextBusinessDay));
    const toggling = w.user.operate(list, "remindersToggle", { shouldRemind: false });
    const whileToggling = w.user.look(list);
    const togglingReached = w.net.deliver(toggling.request(todo.changeReminders));
    w.net.deliver(w.peer.todo.answer(toggling.request(todo.changeReminders), accepted));
    w.net.leaveInFlight(addingReached.event(todo.taskAdded));
    w.net.leaveInFlight(addingReached.answer(tasksReached));
    w.net.leaveInFlight(togglingReached.answer(settingsReached));
    return { whileAdding, whileToggling };
  },
  then: ({ whileAdding, whileToggling }) =>
    [whileAdding, whileToggling].flatMap((look) => [
      notOffered(look, "add", { title: "Buy bread" }),
      notOffered(look, "remindersToggle", { shouldRemind: false }),
      notOffered(look, "openTask", { taskId: "task-1", title: "Buy milk" }),
    ]),
});

export const retriesAfterListRejections = scenario({
  description: "Let todo reject addTask and changeReminders; the list screen accepts add and remindersToggle again",
  given: milk,
  when: (w) => {
    const { list, tasksReached, settingsReached } = openList(w);
    const add1 = w.user.operate(list, "add", { title: "Buy eggs" });
    w.net.refuse(add1.request(todo.addTask));
    const add2 = w.user.operate(list, "add", { title: "Buy eggs" });
    const add2Request = add2.request(todo.addTask);
    const add2Reached = w.net.deliver(add2Request);
    w.net.deliver(w.peer.todo.answer(add2Request, accepted));
    w.net.deliver(add2Reached.request(calendar.nextBusinessDay));
    w.peer.calendar.leaveUnanswered(add2Reached.request(calendar.nextBusinessDay));
    const toggle1 = w.user.operate(list, "remindersToggle", { shouldRemind: false });
    w.net.refuse(toggle1.request(todo.changeReminders));
    const toggle2 = w.user.operate(list, "remindersToggle", { shouldRemind: false });
    const toggle2Reached = w.net.deliver(toggle2.request(todo.changeReminders));
    w.net.deliver(w.peer.todo.answer(toggle2.request(todo.changeReminders), accepted));
    w.net.leaveInFlight(add2Reached.event(todo.taskAdded));
    w.net.leaveInFlight(add2Reached.answer(tasksReached));
    w.net.leaveInFlight(toggle2Reached.answer(settingsReached));
    return { add2, toggle2 };
  },
  then: ({ add2, toggle2 }) => [
    requested(add2, [requestOf(todo.addTask, { taskId: add2.request(todo.addTask).input.taskId, title: "Buy eggs" })]),
    requested(toggle2, [requestOf(todo.changeReminders, { shouldRemind: false })]),
  ],
});

export const retriesAfterRowRejections = scenario({
  description:
    "Let todo reject completeTask and reopenTask; the list screen accepts complete and reopen on the same task again",
  given: milkAndCompletedEggs,
  when: (w) => {
    const { list, tasksSub, tasksReached } = openList(w);
    const filtering = w.user.operate(list, "filter", { filter: "all" });
    const allSub = filtering.subscription(todo.tasks);
    const allReached = w.net.deliver(allSub);
    w.net.deliver(w.peer.todo.answer(allSub, fulfilled({ tasks: [completedEggsRow, milkRow] })));
    const complete1 = w.user.operate(list, "complete", { taskId: "task-1" });
    w.net.refuse(complete1.request(todo.completeTask));
    const complete2 = w.user.operate(list, "complete", { taskId: "task-1" });
    const complete2Reached = w.net.deliver(complete2.request(todo.completeTask));
    w.net.deliver(w.peer.todo.answer(complete2.request(todo.completeTask), accepted));
    const reopen1 = w.user.operate(list, "reopen", { taskId: "task-2" });
    w.net.refuse(reopen1.request(todo.reopenTask));
    const reopen2 = w.user.operate(list, "reopen", { taskId: "task-2" });
    const reopen2Reached = w.net.deliver(reopen2.request(todo.reopenTask));
    w.net.deliver(w.peer.todo.answer(reopen2.request(todo.reopenTask), accepted));
    w.net.leaveInFlight(filtering.end(tasksSub));
    w.net.leaveInFlight(complete2Reached.event(todo.taskCompleted));
    w.net.leaveInFlight(complete2Reached.answer(tasksReached));
    w.net.leaveInFlight(complete2Reached.answer(allReached));
    w.net.leaveInFlight(reopen2Reached.event(todo.taskReopened));
    w.net.leaveInFlight(reopen2Reached.answer(tasksReached));
    w.net.leaveInFlight(reopen2Reached.answer(allReached));
    return { complete2, reopen2 };
  },
  then: ({ complete2, reopen2 }) => [
    requested(complete2, [requestOf(todo.completeTask, { taskId: "task-1" })]),
    requested(reopen2, [requestOf(todo.reopenTask, { taskId: "task-2" })]),
  ],
});

export const retriesAfterRenameAndDueRejections = scenario({
  description: "Let todo reject renameTask and changeDue; the detail screen accepts rename and due date changes again",
  given: milk,
  when: (w) => {
    const { tasksReached, detail, detailReached } = openDetail(w);
    const rename1 = w.user.operate(detail, "rename", { title: "Buy soy milk" });
    w.net.refuse(rename1.request(todo.renameTask));
    const rename2 = w.user.operate(detail, "rename", { title: "Buy soy milk" });
    const rename2Reached = w.net.deliver(rename2.request(todo.renameTask));
    w.net.deliver(w.peer.todo.answer(rename2.request(todo.renameTask), accepted));
    w.user.operate(detail, "dueToggle");
    const due1 = w.user.operate(detail, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" });
    w.net.refuse(due1.request(todo.changeDue));
    w.user.operate(detail, "dueToggle");
    const due2 = w.user.operate(detail, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" });
    const due2Reached = w.net.deliver(due2.request(todo.changeDue));
    w.net.deliver(w.peer.todo.answer(due2.request(todo.changeDue), accepted));
    w.net.leaveInFlight(rename2Reached.answer(tasksReached));
    w.net.leaveInFlight(rename2Reached.answer(detailReached));
    w.net.leaveInFlight(due2Reached.answer(tasksReached));
    w.net.leaveInFlight(due2Reached.answer(detailReached));
    return { rename2, due2 };
  },
  then: ({ rename2, due2 }) => [
    requested(rename2, [requestOf(todo.renameTask, { taskId: "task-1", title: "Buy soy milk" })]),
    requested(due2, [requestOf(todo.changeDue, { taskId: "task-1", dueAt: "2026-10-27T18:00:00+09:00" })]),
  ],
});

export const retriesAfterCompletionRejections = scenario({
  description:
    "Look at the detail screen while completeTask waits for its answer, and let todo reject completeTask and reopenTask; the screen offers neither complete nor close while waiting, and accepts complete and reopen again after each rejection",
  given: milk,
  when: (w) => {
    const { tasksReached, detail, detailSub, detailReached } = openDetail(w);
    const complete1 = w.user.operate(detail, "complete");
    const busy = w.user.look(detail);
    w.net.refuse(complete1.request(todo.completeTask));
    const complete2 = w.user.operate(detail, "complete");
    const complete2Reached = w.net.deliver(complete2.request(todo.completeTask));
    w.net.deliver(w.peer.todo.answer(complete2.request(todo.completeTask), accepted));
    w.net.deliver(w.peer.todo.answer(detailSub, fulfilled({ task: { ...milkDetail, isCompleted: true } })));
    const reopen1 = w.user.operate(detail, "reopen");
    w.net.refuse(reopen1.request(todo.reopenTask));
    const reopen2 = w.user.operate(detail, "reopen");
    const reopen2Reached = w.net.deliver(reopen2.request(todo.reopenTask));
    w.net.deliver(w.peer.todo.answer(reopen2.request(todo.reopenTask), accepted));
    w.net.leaveInFlight(complete2Reached.event(todo.taskCompleted));
    w.net.leaveInFlight(complete2Reached.answer(tasksReached));
    w.net.leaveInFlight(reopen2Reached.event(todo.taskReopened));
    w.net.leaveInFlight(reopen2Reached.answer(tasksReached));
    w.net.leaveInFlight(reopen2Reached.answer(detailReached));
    return { busy, complete2, reopen2 };
  },
  then: ({ busy, complete2, reopen2 }) => [
    notOffered(busy, "complete"),
    notOffered(busy, "close"),
    requested(complete2, [requestOf(todo.completeTask, { taskId: "task-1" })]),
    requested(reopen2, [requestOf(todo.reopenTask, { taskId: "task-1" })]),
  ],
});

export const keepsEditingAfterDeleteRejected = scenario({
  description: "Let todo reject deleteTask; the detail screen stays open and accepts operations again",
  given: milk,
  when: (w) => {
    const { tasksReached, detail, detailSub, detailReached } = openDetail(w);
    const deleting = w.user.operate(detail, "delete");
    const rejected = w.net.refuse(deleting.request(todo.deleteTask));
    const resubscribed = rejected.subscription(todo.taskDetail);
    const resubscribedReached = w.net.deliver(resubscribed);
    w.net.deliver(w.peer.todo.answer(resubscribed, fulfilled({ task: milkDetail })));
    const completing = w.user.operate(detail, "complete");
    const completingReached = w.net.deliver(completing.request(todo.completeTask));
    w.net.deliver(w.peer.todo.answer(completing.request(todo.completeTask), accepted));
    w.net.leaveInFlight(deleting.end(detailSub));
    w.net.leaveInFlight(completingReached.event(todo.taskCompleted));
    w.net.leaveInFlight(completingReached.answer(tasksReached));
    w.net.leaveInFlight(completingReached.answer(detailReached));
    w.net.leaveInFlight(completingReached.answer(resubscribedReached));
    return { completing };
  },
  then: ({ completing }) => [requested(completing, [requestOf(todo.completeTask, { taskId: "task-1" })])],
});

export const keepsDetailWhenOtherTaskDeleted = scenario({
  description: "Receive taskDeleted for another task while the detail screen is open; the screen stays open",
  given: milkAndCompletedEggs,
  when: (w) => {
    const { tasksReached, detail, detailReached } = openDetail(w);
    const del = w.client.send(todo.deleteTask, { taskId: "task-2" });
    const deleted = w.net.deliver(w.peer.todo.emit(todo.taskDeleted, { taskId: "task-2" }, { resultOf: del }));
    const completing = w.user.operate(detail, "complete");
    const completingReached = w.net.deliver(completing.request(todo.completeTask));
    w.net.deliver(w.peer.todo.answer(completing.request(todo.completeTask), accepted));
    w.net.leaveInFlight(completingReached.event(todo.taskCompleted));
    w.net.leaveInFlight(completingReached.answer(tasksReached));
    w.net.leaveInFlight(completingReached.answer(detailReached));
    return { deleted, completing };
  },
  then: ({ deleted, completing }) => [
    requested(deleted, []),
    requested(completing, [requestOf(todo.completeTask, { taskId: "task-1" })]),
  ],
});

export const openTaskNotReopened = scenario({
  description: "Open an open task on the detail screen; the screen offers no reopen",
  given: milk,
  when: (w) => {
    const { detail } = openDetail(w);
    const look = w.user.look(detail);
    return { look };
  },
  then: ({ look }) => [notOffered(look, "reopen")],
});
