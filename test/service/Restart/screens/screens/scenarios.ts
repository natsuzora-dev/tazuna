import { notOffered, type OutSubscription, requested, run, subscriptionOf } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./data.ts";
import { homeScreen, taskListScreen } from "./screens.ts";

const arranged = given({ start: "2026-10-25T10:00:00+09:00", records: {}, peers: [run(todo, {})] });

const deliverSubscription = arranged.step((w, sub: OutSubscription) => {
  const reached = w.net.deliver(sub);
  w.net.leaveInFlight(reached.answer(reached));
});

export const screensReopen = scenario({
  description:
    "Open the list and restart; the restart closes taskListScreen without ending its subscription to tasks, and homeScreen opens again in home, so the list cannot be closed and homeScreen accepts openList, which subscribes to tasks again",
  given: arranged,
  when: (w) => {
    const home = w.startup.screen(homeScreen);
    const opening = w.user.operate(home, "openList");
    deliverSubscription(w, opening.subscription(todo.tasks));
    const restarting = w.host.restart();
    const closedList = w.user.look(opening.screen(taskListScreen));
    const reopening = w.user.operate(restarting.screen(homeScreen), "openList");
    deliverSubscription(w, reopening.subscription(todo.tasks));
    return { restarting, closedList, reopening };
  },
  then: ({ restarting, closedList, reopening }) => [
    requested(restarting, []),
    notOffered(closedList, "close"),
    requested(reopening, [subscriptionOf(todo.tasks, {})]),
  ],
});
