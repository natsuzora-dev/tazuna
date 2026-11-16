import { type OutRequest, run, type When } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { helpPanel, homeScreen, taskListScreen } from "./screens.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: run(todo, {}) } } as const;
type W = When<typeof given.peers>;

/**
 * The network delivers the subscription to todo. todo's answers and the end of the subscription stay in flight: no line
 * delivers an end that the own service sends to a running peer.
 */
const delivered = (w: W, subscription: OutRequest) => {
  w.net.deliver(subscription);
  w.net.inFlight(subscription);
};

/** The home screen that begin opens, with its subscription to taskCount delivered. */
const openHome = (w: W) => {
  delivered(w, w.begin.request(todo.taskCount));
  return w.begin.screen(homeScreen);
};

export const listClosedByParent = scenario(
  "Open the list at 10:00 and again at 10:02; homeScreen opens one taskListScreen each time it enters listing, and when it exits listing at the one-minute deadline at 10:01, it closes taskListScreen, which ends its subscription to tasks. homeScreen keeps its subscription to taskCount while taskListScreen is open",
  {
    given,
    when: (w) => {
      const home = openHome(w);
      delivered(w, w.user.operate(home, "openList").request(todo.tasks));
      w.clock.at("2026-10-25T10:02:00+09:00");
      delivered(w, w.user.operate(home, "openList").request(todo.tasks));
    },
    then: () => [],
  },
);

export const modalChild = scenario(
  "Open the list, close it, and count all; taskListScreen, which homeScreen opened as modal, closes on the operation close, and homeScreen goes back to home through onDone, accepts the operation countAll, and subscribes to taskCount again with all",
  {
    given,
    when: (w) => {
      const home = openHome(w);
      const opening = w.user.operate(home, "openList");
      delivered(w, opening.request(todo.tasks));
      w.user.operate(opening.screen(taskListScreen), "close");
      delivered(w, w.user.operate(home, "countAll").request(todo.taskCount));
    },
    then: () => [],
  },
);

export const nonModalChild = scenario(
  "Open the help, count all, and close the help; while helpPanel, which is not modal, is open, homeScreen still accepts the operation countAll and subscribes to taskCount again with all, and helpPanel accepts the operation closeHelp",
  {
    given,
    when: (w) => {
      const home = openHome(w);
      const opening = w.user.operate(home, "openHelp");
      delivered(w, w.user.operate(home, "countAll").request(todo.taskCount));
      w.user.operate(opening.screen(helpPanel), "closeHelp");
    },
    then: () => [],
  },
);
