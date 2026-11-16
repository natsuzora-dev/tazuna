import { listTasks, orderedTaskGroups, scenario, tagScreen, tagTask, taskGroups } from "./todo.ts";

export const listed = scenario(
  "List the tasks; verify treats as matching an implementation trace that orders the elements of titles and tags differently, and orders differently the entries with the same day; no violation",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.client.send(listTasks, {});
    },
    then: () => [],
  },
);

export const grouped = scenario(
  "Ask for the task groups, tag a task, and pick tags; verify does not compare the order of the elements of a bag value, also inside objects in arrays and inside z.union, optional, nullable, and default, nor, in arrays, the order of elements of a sortedBy value with the same at. It does not compare the order of the bag elements in the command input and the operation payload of in lines either; no violation",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      const tags = w.begin.screen(tagScreen);
      w.client.call(taskGroups, {});
      w.client.send(tagTask, { tags: ["home", "store"] });
      w.user.operate(tags, "pick", { tags: ["home", "store"] });
    },
    then: () => [],
  },
);

export const groupedSixTimes = scenario(
  "Ask for orderedTaskGroups six times; the implementation trace of this scenario answers with a different number of bag elements, a different order of array elements, a different order of sortedBy elements with different at values, and a different number of elements of a default bag, so verify reports Mismatch.output",
  {
    given: { start: "2026-10-25T00:00:00Z", records: {}, peers: {} },
    when: (w) => {
      w.client.call(orderedTaskGroups, {});
      w.client.call(orderedTaskGroups, {});
      w.client.call(orderedTaskGroups, {});
      w.client.call(orderedTaskGroups, {});
      w.client.call(orderedTaskGroups, {});
      w.client.call(orderedTaskGroups, {});
    },
    then: () => [],
  },
);
