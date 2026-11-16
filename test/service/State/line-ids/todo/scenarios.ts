import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const twoTasks = scenario(
  "Add two tasks, the second with the id c1; test gives each line without an id an id of its name, or its kind for a line without a name, and its ordinal, such as addTask#1, answer#1, and taskAdded#1, and keeps the id c1 that the scenario gives. createKey returns Note-1 and Note-2, and the snapshot writes each value in created of the line where it first appears",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1" }),
    send(addTask, { taskId: "task-2" }, { id: "c1" }),
  ],
);

export const machineKeys = scenario(
  "Add the task pin-1; createKey in the assign of the transition of tagger returns Tag-1, and createKey in the input of the sends of tagging returns Tag-2. The automations and machines share the createKey count of each entity, which is separate from the count of Note",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, { taskId: "pin-1" })],
);
