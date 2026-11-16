import { endOf, type OutRequest, requested, run, subscription, type When } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { listScreen } from "./listScreen.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: run(todo, {}) } } as const;
type W = When<typeof given.peers>;

/** The network delivers the subscription to todo; todo's later messages on it stay in flight. */
const delivered = (w: W, sub: OutRequest) => {
  w.net.deliver(sub);
  w.net.inFlight(sub);
};
/** The subscriptions that begin opened reach todo. */
const subscribed = (w: W) => {
  const tasksSub = w.begin.request(todo.tasks);
  const countSub = w.begin.request(todo.taskCount);
  w.net.deliver(tasksSub);
  w.net.deliver(countSub);
  return { list: w.begin.screen(listScreen), tasksSub, countSub };
};
const tasksShown = (w: W, sub: OutRequest<typeof todo.tasks>) =>
  w.peer.todo.answer(sub, { result: "fulfilled", output: { taskIds: [] } });
const countShown = (w: W, sub: OutRequest<typeof todo.taskCount>) =>
  w.peer.todo.answer(sub, { result: "fulfilled", output: { count: 0 } });

export const answersOneByOne = scenario(
  "Answer tasks, operate showAll, answer taskCount, and operate showAll; listScreen processes the answers to its subscriptions one at a time as inputs. With only the tasks answer, listScreen is still in loading and does not accept showAll. After the taskCount answer moves it to ready, showAll ends the subscription to tasks and subscribes to tasks again with the changed filter in its input",
  {
    given,
    when: (w) => {
      const { list, tasksSub, countSub } = subscribed(w);
      tasksShown(w, tasksSub);
      const loading = w.user.operate(list, "showAll");
      countShown(w, countSub);
      const ready = w.user.operate(list, "showAll");
      delivered(w, ready.request(todo.tasks));
      // The end of the first tasks subscription stays in flight: no line delivers an end that the own service sends.
      w.net.inFlight(tasksSub);
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
      const { list, tasksSub, countSub } = subscribed(w);
      tasksShown(w, tasksSub);
      countShown(w, countSub);
      const reloading = w.user.operate(list, "reload");
      const peeking = w.user.operate(list, "peek");
      return { reloading, peeking };
    },
    then: ({ reloading, peeking }) => [requested(reloading, []), requested(peeking, [])],
  },
);
