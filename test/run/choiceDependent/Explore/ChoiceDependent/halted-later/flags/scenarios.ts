import { addTask, flagText, scenario } from "./flags.ts";

export const addOneThenRead = scenario(
  "Add a task, whose processing reaches raise and lower in either order, then read the flag, whose text breaks the output schema and halts flags; the halt at the last line does not hide the stepOrder of the first",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Flag: { isOn: false } }, peers: [] },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.call(flagText, {});
    },
    then: () => [],
  },
);
