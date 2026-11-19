import { accepted, external, fulfilled, type When } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { listScreen } from "./listScreen.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: external(todo) } } as const;
type W = When<typeof given.peers>;

const deliveredList = (w: W, ...taskIds: string[]) => {
  const tasks = w.startup.subscription(todo.tasks);
  w.net.deliver(tasks);
  w.net.deliver(w.peer.todo.answer(tasks, fulfilled({ taskIds })));
  return w.startup.screen(listScreen);
};

export const routedByKey = scenario(
  "Show task-1 and task-2, complete task-1 twice and task-2 once, and answer; the operation complete reaches only the copy whose key taskId equals the taskId of the payload. The copy of task-1 does not accept a second complete while it waits in completing for the answer. listScreen accepts complete for task-2 while the copy of task-1 waits",
  {
    given,
    when: (w) => {
      const list = deliveredList(w, "task-1", "task-2");
      const first = w.user.operate(list, "complete", { taskId: "task-1" }).request(todo.completeTask);
      w.user.operate(list, "complete", { taskId: "task-1" });
      const second = w.user.operate(list, "complete", { taskId: "task-2" }).request(todo.completeTask);
      w.net.deliver(second);
      w.net.deliver(w.peer.todo.answer(second, accepted));
      w.net.deliver(first);
      w.net.deliver(w.peer.todo.answer(first, accepted));
      const third = w.user.operate(list, "complete", { taskId: "task-1" }).request(todo.completeTask);
      w.net.deliver(third);
      w.peer.todo.leaveUnanswered(third);
    },
    then: () => [],
  },
);

export const noCopyForKey = scenario(
  "Show task-1 and complete task-3; the operation complete for task-3, which has no copy, reaches no copy",
  {
    given,
    when: (w) => {
      w.user.operate(deliveredList(w, "task-1"), "complete", { taskId: "task-3" });
    },
    then: () => [],
  },
);

export const withoutKeyFields = scenario(
  "Show two tasks and complete all; the operation completeAll, whose payload has no taskId, reaches every copy",
  {
    given,
    when: (w) => {
      const all = w.user.operate(deliveredList(w, "task-1", "task-2"), "completeAll");
      const first = all.request(todo.completeTask, { taskId: "task-1" });
      const second = all.request(todo.completeTask, { taskId: "task-2" });
      w.net.deliver(first);
      w.peer.todo.leaveUnanswered(first);
      w.net.deliver(second);
      w.peer.todo.leaveUnanswered(second);
    },
    then: () => [],
  },
);
