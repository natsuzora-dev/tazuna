import { addTask, scenario } from "./todo.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: { Task: [], Note: [], Tag: [] }, peers: [] } as const;

export const twoTasks = scenario(
  "Add two tasks; test gives each line an id of its name, or its kind for a line without a name, and its ordinal, such as addTask#1, answer#1, and taskAdded#1. createKey returns todo/Note-1 and todo/Note-2, and the snapshot writes each value in created of the line where it first appears",
  {
    given,
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.send(addTask, { taskId: "task-2" });
    },
    then: () => [],
  },
);

export const machineKeys = scenario(
  "Add the task pin-1; createKey in the assign of the transition of tagger returns todo/Tag-1, and createKey in the input of the sends of tagging returns todo/Tag-2. The automations and machines share the createKey count of each entity, which is separate from the count of Note",
  {
    given,
    when: (w) => {
      w.client.send(addTask, { taskId: "pin-1" });
    },
    then: () => [],
  },
);
