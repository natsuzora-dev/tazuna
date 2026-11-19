import { notOffered, offered } from "@natsuzora-dev/tazuna";
import { board, confirmDialog, listScreen, panel, scenario } from "./screens.ts";

const given = { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} } as const;

export const pickAndCancel = scenario("Pick a shown task, open the dialog, and cancel it; no violation", {
  given,
  when: (w) => {
    const list = w.startup.screen(listScreen);
    w.user.operate(list, "pick", { taskId: "task-1" });
    const cleared = w.user.operate(list, "clear");
    w.user.operate(cleared.screen(confirmDialog), "cancel");
    w.user.operate(list, "pick", { taskId: "task-2" });
  },
  then: () => [],
});

export const cannotPickUnaccepted = scenario(
  "Look at the list before and while the dialog covers it; the list offers no task that it does not show, and no task while the dialog covers it; no violation",
  {
    given,
    when: (w) => {
      const list = w.startup.screen(listScreen);
      const before = w.user.look(list);
      w.user.operate(list, "clear");
      const covered = w.user.look(list);
      return { before, covered };
    },
    then: ({ before, covered }) => [
      notOffered(before, "pick", { taskId: "task-3" }),
      notOffered(covered, "pick", { taskId: "task-1" }),
    ],
  },
);

export const cancelUnopened = scenario(
  "Cancel the dialog twice; the first cancel closes it, so the second operates a screen that is not open, and test reports unopenedScreen",
  {
    given,
    when: (w) => {
      const dialog = w.user.operate(w.startup.screen(listScreen), "clear").screen(confirmDialog);
      w.user.operate(dialog, "cancel");
      w.user.operate(dialog, "cancel");
    },
    then: () => [],
  },
);

export const pickUnderDialog = scenario("Pick a task while the dialog covers the list; test reports coveredByModal", {
  given,
  when: (w) => {
    const list = w.startup.screen(listScreen);
    w.user.operate(list, "clear");
    w.user.operate(list, "pick", { taskId: "task-1" });
  },
  then: () => [],
});

export const pickUnoffered = scenario("Pick a task that the list does not show; test reports unofferedPayload", {
  given,
  when: (w) => {
    w.user.operate(w.startup.screen(listScreen), "pick", { taskId: "task-3" });
  },
  then: () => [],
});

export const closeEarlierPanel = scenario(
  "Open a panel from each region and close the earlier one by its handle; both are open, so the operation line names it by nth; no violation",
  {
    given,
    when: (w) => {
      const boardScreen = w.startup.screen(board);
      const left = w.user.operate(boardScreen, "openLeft").screen(panel);
      w.user.operate(boardScreen, "openRight");
      const looked = w.user.look(left);
      w.user.operate(left, "close");
      return { looked };
    },
    then: ({ looked }) => [offered(looked, "close")],
  },
);

export const cancelReopened = scenario(
  "Open the dialog, cancel it, and open it again; the reopened dialog takes the closed one's name, and the second cancel operates it; no violation",
  {
    given,
    when: (w) => {
      const list = w.startup.screen(listScreen);
      w.user.operate(w.user.operate(list, "clear").screen(confirmDialog), "cancel");
      w.user.operate(w.user.operate(list, "clear").screen(confirmDialog), "cancel");
      w.user.operate(list, "pick", { taskId: "task-1" });
    },
    then: () => [],
  },
);
