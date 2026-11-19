import { addTask, scenario } from "./marks.ts";

export const addSeventh = scenario({
  description:
    "Add a seventh task; markEveryTask creates seven mark keys from a Bag callback, which no content tells apart, so comparing the reversed answer tries more renamings than bindingLimit and test reports reversedBagBindings",
  given: {
    start: "2026-10-25T09:00:00+09:00",
    records: {
      Task: [
        { id: "task-1" },
        { id: "task-2" },
        { id: "task-3" },
        { id: "task-4" },
        { id: "task-5" },
        { id: "task-6" },
      ],
      Mark: [],
    },
    peers: [],
  },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-7" });
  },
  then: () => [],
});
