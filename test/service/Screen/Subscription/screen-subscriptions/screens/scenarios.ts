import { endOf, type OutSubscription, requested, run, subscription, type When } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { listScreen } from "./listScreen.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: run(todo, {}) } } as const;
type W = When<typeof given.peers>;

const deliverSubscription = (w: W, sub: OutSubscription) => {
  const reached = w.net.deliver(sub);
  w.net.inFlight(reached.answer(reached));
};
const deliverBeginSubscriptions = (w: W) => {
  const tasksSub = w.begin.subscription(todo.tasks);
  const countSub = w.begin.subscription(todo.taskCount);
  w.net.deliver(tasksSub);
  w.net.deliver(countSub);
  return { list: w.begin.screen(listScreen), tasksSub, countSub };
};
const deliverTasksShown = (w: W, sub: OutSubscription<typeof todo.tasks>) =>
  w.net.deliver(w.peer.todo.answer(sub, { result: "fulfilled", output: { taskIds: [] } }));
const deliverCountShown = (w: W, sub: OutSubscription<typeof todo.taskCount>) =>
  w.net.deliver(w.peer.todo.answer(sub, { result: "fulfilled", output: { count: 0 } }));

export const answersOneByOne = scenario(
  "Answer tasks, operate showAll, answer taskCount, and operate showAll; listScreen processes the answers to its subscriptions one at a time as inputs. With only the tasks answer, listScreen is still in loading and does not accept showAll. After the taskCount answer moves it to ready, showAll ends the subscription to tasks and subscribes to tasks again with the changed filter in its input",
  {
    given,
    when: (w) => {
      const { list, tasksSub, countSub } = deliverBeginSubscriptions(w);
      deliverTasksShown(w, tasksSub);
      const loading = w.user.operate(list, "showAll");
      deliverCountShown(w, countSub);
      const ready = w.user.operate(list, "showAll");
      w.net.inFlight(ready.end(tasksSub));
      deliverSubscription(w, ready.subscription(todo.tasks));
      return { tasksSub, loading, ready };
    },
    then: ({ tasksSub, loading, ready }) => [
      requested(loading, []),
      requested(ready, [endOf(tasksSub), subscription(todo.tasks, { filter: "all" })]),
    ],
  },
);

export const subscriptionsAfterTransitions = scenario(
  "Answer, reload, and peek; listScreen compares its subscriptions with the shows of the state after all transitions of a message. Reloading reenters open, but the input of tasks stays the same, so listScreen does not subscribe again. Peeking passes through peeking, so listScreen does not subscribe to allTasks",
  {
    given,
    when: (w) => {
      const { list, tasksSub, countSub } = deliverBeginSubscriptions(w);
      deliverTasksShown(w, tasksSub);
      deliverCountShown(w, countSub);
      const reloading = w.user.operate(list, "reload");
      const peeking = w.user.operate(list, "peek");
      return { reloading, peeking };
    },
    then: ({ reloading, peeking }) => [requested(reloading, []), requested(peeking, [])],
  },
);
