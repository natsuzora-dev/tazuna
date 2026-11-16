import { type CausedLine, external, notOffered, type When } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { editScreen } from "./editScreen.ts";
import { taskScreen } from "./taskScreen.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: external(todo) } } as const;
type W = When<typeof given.peers>;

/** todo answers the task subscription of the task screen that begin opened. */
const shown = (w: W, isCompleted: boolean) =>
  w.peer.todo.answer(w.begin.request(todo.task), { result: "fulfilled", output: { isCompleted } });
/** todo never answers the task subscription. */
const neverShown = (w: W) => w.peer.todo.leaveUnanswered(w.begin.request(todo.task));
const accepted = (w: W, line: CausedLine) =>
  w.peer.todo.answer(line.request(todo.completeTask), { result: "accepted" });

export const offersDecide = scenario(
  "Look at complete before the task answer and while a completed task is shown; the offers of complete return [] before the task answer arrives and while a completed task is shown, so taskScreen does not offer complete then. innermostOffers shows that taskScreen accepts complete and sends completeTask while an open task is shown: an external peer answers a subscription only once",
  {
    given,
    when: (w) => {
      const task = w.begin.screen(taskScreen);
      const beforeAnswer = w.user.look(task);
      shown(w, true);
      const completedShown = w.user.look(task);
      return { beforeAnswer, completedShown };
    },
    then: ({ beforeAnswer, completedShown }) => [
      notOffered(beforeAnswer, "complete"),
      notOffered(completedShown, "complete"),
    ],
  },
);

export const innermostOffers = scenario(
  "Show an open task, complete it, and accept; after completeTask is accepted and taskScreen enters completed, the offers of completed apply instead of those of root, so taskScreen does not accept complete even though the task answer shows an open task",
  {
    given,
    when: (w) => {
      const task = w.begin.screen(taskScreen);
      shown(w, false);
      accepted(w, w.user.operate(task, "complete"));
      return { look: w.user.look(task) };
    },
    then: ({ look }) => [notOffered(look, "complete")],
  },
);

export const acceptedWithoutTransition = scenario(
  "Show an open task and operate complete twice; the offers of complete of root return [{}] while taskScreen waits for the answer to completeTask, so taskScreen accepts complete, but completing has no transition on complete, so it sends no second completeTask",
  {
    given,
    when: (w) => {
      const task = w.begin.screen(taskScreen);
      shown(w, false);
      const first = w.user.operate(task, "complete");
      w.user.operate(task, "complete");
      accepted(w, first);
    },
    then: () => [],
  },
);

export const unionOfRegionOffers = scenario(
  "Operate save on editScreen twice; while editScreen is in both renaming and completing, the offers of save of completing return [{}], so editScreen accepts save even though the offers of save of renaming return []",
  {
    given,
    when: (w) => {
      const edit = w.begin.screen(editScreen);
      w.user.operate(edit, "save");
      w.user.operate(edit, "save");
      neverShown(w);
    },
    then: () => [],
  },
);

export const parentlessSideBySide = scenario(
  "Save on editScreen, show an open task, complete on taskScreen, and save again; taskScreen and editScreen have no parent, so both are topmost screens, and taskScreen accepts complete after the save of editScreen, and then editScreen accepts save",
  {
    given,
    when: (w) => {
      const edit = w.begin.screen(editScreen);
      w.user.operate(edit, "save");
      shown(w, false);
      const completing = w.user.operate(w.begin.screen(taskScreen), "complete");
      w.user.operate(edit, "save");
      w.peer.todo.leaveUnanswered(completing.request(todo.completeTask));
    },
    then: () => [],
  },
);

export const datetimeOffers = scenario(
  "Operate remind on taskScreen; its offers return the at as a Temporal.Instant, and the list of accepted operations and the operation line of the trace hold that at as an ISO 8601 string",
  {
    given,
    when: (w) => {
      w.user.operate(w.begin.screen(taskScreen), "remind", { at: "2026-10-25T03:00:00Z" });
      neverShown(w);
    },
    then: () => [],
  },
);
