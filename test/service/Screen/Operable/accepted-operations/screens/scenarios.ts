import { accepted, external, fulfilled, notOffered, type ProcessingLine, parseInstant } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./data.ts";
import { editScreen } from "./editScreen.ts";
import { taskScreen } from "./taskScreen.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [external(todo)] });

const deliverTaskSubscription = arranged.step((w) => w.net.deliver(w.startup.subscription(todo.task)));
const deliverShown = arranged.step((w, isCompleted: boolean) =>
  w.net.deliver(w.peer.todo.answer(w.startup.subscription(todo.task), fulfilled({ isCompleted }))),
);
const deliverNeverShown = arranged.step((w) => {
  deliverTaskSubscription(w);
  w.peer.todo.leaveUnanswered(w.startup.subscription(todo.task));
});
const deliverAccepted = arranged.step((w, line: ProcessingLine) => {
  const complete = line.request(todo.completeTask);
  w.net.deliver(complete);
  w.net.deliver(w.peer.todo.answer(complete, accepted()));
});

export const offersDecide = scenario({
  description:
    "Look at complete before the task answer and while a completed task is shown, and operate it while an open task is shown; the offers of complete return [] before the task answer arrives and while a completed task is shown, so taskScreen does not offer complete then. While an open task is shown, taskScreen accepts complete and sends completeTask",
  given: arranged,
  when: (w) => {
    const task = w.startup.screen(taskScreen);
    const beforeAnswer = w.user.look(task);
    deliverTaskSubscription(w);
    deliverShown(w, true);
    const completedShown = w.user.look(task);
    deliverShown(w, false);
    deliverAccepted(w, w.user.operate(task, "complete"));
    return { beforeAnswer, completedShown };
  },
  then: ({ beforeAnswer, completedShown }) => [
    notOffered(beforeAnswer, "complete"),
    notOffered(completedShown, "complete"),
  ],
});

export const innermostOffers = scenario({
  description:
    "Show an open task, complete it, and accept; after completeTask is accepted and taskScreen enters completed, the offers of completed apply instead of those of root, so taskScreen does not accept complete even though the task answer shows an open task",
  given: arranged,
  when: (w) => {
    const task = w.startup.screen(taskScreen);
    deliverTaskSubscription(w);
    deliverShown(w, false);
    deliverAccepted(w, w.user.operate(task, "complete"));
    return { look: w.user.look(task) };
  },
  then: ({ look }) => [notOffered(look, "complete")],
});

export const unionOfRegionOffers = scenario({
  description:
    "Operate save on editScreen twice; while editScreen is in both renaming and completing, the offers of save of completing are any, so editScreen accepts save even though the offers of save of renaming are none",
  given: arranged,
  when: (w) => {
    const edit = w.startup.screen(editScreen);
    w.user.operate(edit, "save");
    w.user.operate(edit, "save");
    deliverNeverShown(w);
  },
  then: () => [],
});

export const parentlessSideBySide = scenario({
  description:
    "Save on editScreen, show an open task, complete on taskScreen, and save again; taskScreen and editScreen have no parent, so both are topmost screens, and taskScreen accepts complete after the save of editScreen, and then editScreen accepts save",
  given: arranged,
  when: (w) => {
    const edit = w.startup.screen(editScreen);
    w.user.operate(edit, "save");
    deliverTaskSubscription(w);
    deliverShown(w, false);
    const completing = w.user.operate(w.startup.screen(taskScreen), "complete");
    w.user.operate(edit, "save");
    const complete = completing.request(todo.completeTask);
    w.net.deliver(complete);
    w.peer.todo.leaveUnanswered(complete);
  },
  then: () => [],
});
