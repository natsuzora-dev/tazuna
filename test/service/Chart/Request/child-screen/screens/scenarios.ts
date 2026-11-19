import { run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./data.ts";
import { helpPanel, homeScreen, taskListScreen } from "./screens.ts";

const arranged = given({ start: "2026-10-25T10:00:00+09:00", records: {}, peers: [run(todo, {})] });

export const listClosedByParent = scenario(
  "Open the list at 10:00 and again at 10:02; homeScreen opens one taskListScreen each time it enters listing, and when it exits listing at the one-minute deadline at 10:01, it closes taskListScreen, which ends its subscription to tasks. homeScreen keeps its subscription to taskCount while taskListScreen is open",
  {
    given: arranged,
    when: (w) => {
      const home = w.startup.screen(homeScreen);
      const count = w.net.deliver(w.startup.subscription(todo.taskCount));
      w.net.leaveInFlight(count.answer(count));
      const firstList = w.user.operate(home, "openList").subscription(todo.tasks);
      const first = w.net.deliver(firstList);
      w.net.leaveInFlight(first.answer(first));
      const closing = w.clock.at("2026-10-25T10:02:00+09:00");
      w.net.leaveInFlight(closing.end(firstList));
      const second = w.net.deliver(w.user.operate(home, "openList").subscription(todo.tasks));
      w.net.leaveInFlight(second.answer(second));
    },
    then: () => [],
  },
);

export const modalChild = scenario(
  "Open the list, close it, and count all; taskListScreen, which homeScreen opened as modal, closes on the operation close, and homeScreen goes back to home through onDone, accepts the operation countAll, and subscribes to taskCount again with all",
  {
    given: arranged,
    when: (w) => {
      const home = w.startup.screen(homeScreen);
      const countSubscription = w.startup.subscription(todo.taskCount);
      const count = w.net.deliver(countSubscription);
      w.net.leaveInFlight(count.answer(count));
      const opening = w.user.operate(home, "openList");
      const list = w.net.deliver(opening.subscription(todo.tasks));
      w.net.leaveInFlight(list.answer(list));
      const closing = w.user.operate(opening.screen(taskListScreen), "close");
      w.net.leaveInFlight(closing.end(opening.subscription(todo.tasks)));
      const countingAll = w.user.operate(home, "countAll");
      w.net.leaveInFlight(countingAll.end(countSubscription));
      const all = w.net.deliver(countingAll.subscription(todo.taskCount));
      w.net.leaveInFlight(all.answer(all));
    },
    then: () => [],
  },
);

export const nonModalChild = scenario(
  "Open the help, count all, and close the help; while helpPanel, which is not modal, is open, homeScreen still accepts the operation countAll and subscribes to taskCount again with all, and helpPanel accepts the operation closeHelp",
  {
    given: arranged,
    when: (w) => {
      const home = w.startup.screen(homeScreen);
      const countSubscription = w.startup.subscription(todo.taskCount);
      const count = w.net.deliver(countSubscription);
      w.net.leaveInFlight(count.answer(count));
      const opening = w.user.operate(home, "openHelp");
      const countingAll = w.user.operate(home, "countAll");
      w.net.leaveInFlight(countingAll.end(countSubscription));
      const all = w.net.deliver(countingAll.subscription(todo.taskCount));
      w.net.leaveInFlight(all.answer(all));
      w.user.operate(opening.screen(helpPanel), "closeHelp");
    },
    then: () => [],
  },
);
