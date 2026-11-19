import { addTasks, scenario } from "./count.ts";

export const addTwo = scenario({
  description:
    "addTasks emits a and b as a tie. With a first, the panel enters and leaves open within the tie and opens the detail only on claimed; with b first, it opens the detail at the tie and claimed reopens it. Either order leaves one detail open under the same name, so test reports nothing",
  given: { start: "2026-10-25T09:00:00Z", records: {}, peers: [] },
  when: (w) => {
    w.client.send(addTasks, { taskIds: ["a", "b"] });
  },
  then: () => [],
});
