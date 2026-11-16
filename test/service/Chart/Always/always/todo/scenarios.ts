import { skip } from "@natsuzora-dev/tazuna";
import { screens } from "../screens/contract.ts";
import { addTask, completeTask, openRows, scenario, signal } from "./todo.ts";

const given = {
  start: "2026-10-25T10:00:00+09:00",
  records: { Task: [], Signal: [] },
  peers: { screens: skip(screens, "the screens' subscriptions are the screens' scenario") },
} as const;

export const tooManyTasks = scenario(
  "Add three tasks, complete one, and add another; workload receives no event but evaluates its always guards again each time the records change, so it enters warning and warns after the third addTask, goes back to quiet after completeTask, and warns again after the next addTask",
  {
    given,
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.send(addTask, { taskId: "task-2" });
      w.client.send(addTask, { taskId: "task-3" });
      w.client.send(completeTask, { taskId: "task-1" });
      w.client.send(addTask, { taskId: "task-4" });
    },
    then: () => [],
  },
);

export const fourTasks = scenario(
  "Add four tasks; after the fourth addTask, the always guards of both regions of review hold in the same configuration, so review takes the two transitions together in one microstep and sends count and list once each",
  {
    given,
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.send(addTask, { taskId: "task-2" });
      w.client.send(addTask, { taskId: "task-3" });
      w.client.send(addTask, { taskId: "task-4" });
    },
    then: () => [],
  },
);

export const copiesSettle = scenario(
  "Add the task chain and then another task; chain enters p. When the always evaluation settles the copies, the copy a of writer enters and adds a to names, which changes the items of reader. The evaluation repeats until no copy changes and no transition has a guard that holds, so the copy a of reader starts in the same evaluation and sends count in this message. The next addTask sends nothing",
  {
    given,
    when: (w) => {
      w.client.send(addTask, { taskId: "chain" });
      w.client.send(addTask, { taskId: "task-1" });
    },
    then: () => [],
  },
);

export const settlesBeforeEvent = scenario(
  "Send signal; signal creates a Signal record, so gate evaluates its always guards at the start of the processing step that receives signalled and enters ready. gate therefore receives signalled in ready, not in idle, enters opened, and sends count",
  {
    given,
    when: (w) => {
      w.client.send(signal, { signalId: "signal-1" });
    },
    then: () => [],
  },
);

export const copiesSettleOnContext = scenario(
  "Open the rows; on rowsOpened, the top-level on transition of the machine rows writes isOpen without a target. No copy takes a transition, but the copy a evaluates its always guards again, enters marking, and marks. When the onAccepted transition of markRow in the copy a writes a to done, the copy b also evaluates its always guards again, enters marking, and marks",
  {
    given,
    when: (w) => {
      w.client.send(openRows, {});
    },
    then: () => [],
  },
);
