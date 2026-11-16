import { notOffered, type OutRequest, requested, run, subscription, type When } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { homeScreen, taskListScreen } from "./screens.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: run(todo, {}) } } as const;
type W = When<typeof given.peers>;

/** The network delivers the subscription to todo; todo's answers on it stay in flight. */
const delivered = (w: W, sub: OutRequest) => {
  w.net.deliver(sub);
  w.net.inFlight(sub);
};

export const screensReopen = scenario(
  "Open the list and restart; the restart closes taskListScreen without ending its subscription to tasks, and homeScreen opens again in home, so the list cannot be closed and homeScreen accepts openList, which subscribes to tasks again",
  {
    given,
    when: (w) => {
      const home = w.begin.screen(homeScreen);
      const opening = w.user.operate(home, "openList");
      delivered(w, opening.request(todo.tasks));
      const restarting = w.host.restart();
      const closedList = w.user.look(opening.screen(taskListScreen));
      const reopening = w.user.operate(home, "openList");
      delivered(w, reopening.request(todo.tasks));
      return { restarting, closedList, reopening };
    },
    then: ({ restarting, closedList, reopening }) => [
      requested(restarting, []),
      notOffered(closedList, "close"),
      requested(reopening, [subscription(todo.tasks, {})]),
    ],
  },
);
