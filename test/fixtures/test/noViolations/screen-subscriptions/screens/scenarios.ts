import {
  endOf,
  fulfilled,
  type OutSubscription,
  parseInstant,
  requested,
  run,
  subscriptionOf,
} from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./data.ts";
import { listScreen } from "./listScreen.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [run(todo, {})] });

const deliverSubscription = arranged.step((w, sub: OutSubscription) => {
  const reached = w.net.deliver(sub);
  w.net.leaveInFlight(reached.answer(reached));
});
const deliverBeginSubscriptions = arranged.step((w) => {
  const tasksSub = w.startup.subscription(todo.tasks);
  const countSub = w.startup.subscription(todo.taskCount);
  w.net.deliver(tasksSub);
  w.net.deliver(countSub);
  return { list: w.startup.screen(listScreen), tasksSub, countSub };
});
const deliverTasksShown = arranged.step((w, sub: OutSubscription<typeof todo.tasks>) =>
  w.net.deliver(w.peer.todo.answer(sub, fulfilled({ taskIds: [] }))),
);
const deliverCountShown = arranged.step((w, sub: OutSubscription<typeof todo.taskCount>) =>
  w.net.deliver(w.peer.todo.answer(sub, fulfilled({ count: 0 }))),
);

export const answersOneByOne = scenario({
  description:
    "Answer tasks, operate showAll, answer taskCount, and operate showAll; listScreen processes the answers to its subscriptions one at a time as inputs. With only the tasks answer, listScreen is still in loading and does not accept showAll. After the taskCount answer moves it to ready, showAll ends the subscription to tasks and subscribes to tasks again with the changed filter in its input",
  given: arranged,
  when: (w) => {
    const { list, tasksSub, countSub } = deliverBeginSubscriptions(w);
    deliverTasksShown(w, tasksSub);
    const loading = w.user.operate(list, "showAll");
    deliverCountShown(w, countSub);
    const ready = w.user.operate(list, "showAll");
    w.net.leaveInFlight(ready.end(tasksSub));
    deliverSubscription(w, ready.subscription(todo.tasks));
    return { tasksSub, loading, ready };
  },
  then: ({ tasksSub, loading, ready }) => [
    requested(loading, []),
    requested(ready, [endOf(tasksSub), subscriptionOf(todo.tasks, { filter: "all" })]),
  ],
});

export const subscriptionsAfterTransitions = scenario({
  description:
    "Answer, reload, and peek; listScreen compares its subscriptions with the shows of the state after all transitions of a message. Reloading reenters open, but the input of tasks stays the same, so listScreen does not subscribe again. Peeking passes through peeking, so listScreen does not subscribe to allTasks",
  given: arranged,
  when: (w) => {
    const { list, tasksSub, countSub } = deliverBeginSubscriptions(w);
    deliverTasksShown(w, tasksSub);
    deliverCountShown(w, countSub);
    const reloading = w.user.operate(list, "reload");
    const peeking = w.user.operate(list, "peek");
    return { reloading, peeking };
  },
  then: ({ reloading, peeking }) => [requested(reloading, []), requested(peeking, [])],
});
