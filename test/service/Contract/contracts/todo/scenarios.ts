import { addTask, given, pinTask, pinTaskByTitle, renameTask, scenario, taskTitles } from "./todo.ts";

const arranged = given({
  start: "2026-10-25T10:00:00+09:00",
  records: { Task: [], Board: { pinned: null, pins: 0 } },
  peers: [],
});

export const renamedThroughBlank = scenario(
  "Add two tasks, rename the first, and list the titles; the first event of renameTask empties the title and breaks titleNotBlank, but todo checks the invariants when the command ends, so no violation is reported. The ensures renamed compares the title before the write, which bound reads, with the title after it, which records reads",
  {
    given: arranged,
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
      w.client.send(renameTask, { taskId: "task-1", title: "Buy bread" });
      w.client.call(taskTitles, {});
    },
    then: () => [],
  },
);

export const pinnedTwice = scenario(
  "Add a task and pin it twice; the record of the single entity Board exists from the start of todo, and pinTask reads pins of Board and increments it. After both pinTask commands, Board satisfies its invariant fewPins, and pinned refers to the existing task-1",
  {
    given: arranged,
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.client.send(pinTask, { taskId: "task-1" });
      w.client.send(pinTask, { taskId: "task-1" });
    },
    then: () => [],
  },
);

export const pinnedByMissingTitle = scenario(
  "Add a task and pin tasks by a missing and an existing title; the title in the input of pinTaskByTitle is not a ref, so a missing title is not not-found. The binds task searches by title and gets null, so pinTaskByTitle is rejected with requires whose reason is the binds name task. pinTaskByTitle with an existing title is accepted",
  {
    given: arranged,
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.client.send(pinTaskByTitle, { title: "Buy eggs" });
      w.client.send(pinTaskByTitle, { title: "Buy milk" });
    },
    then: () => [],
  },
);
