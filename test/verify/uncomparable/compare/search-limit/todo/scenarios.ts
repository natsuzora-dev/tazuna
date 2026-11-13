import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTasks } from "./todo.ts";

export const addTen = scenario(
  "Add ten tasks at once; the implementation trace of this scenario gives two seen events one key, so no pairing renames the keys one to one, and the search for one stops after searchLimit steps, so verify reports searchLimit",
  [
    at("2026-10-25T00:00:00Z"),
    send(addTasks, { taskIds: ["t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7", "t8", "t9"] }),
  ],
);
