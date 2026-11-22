import { answered, fulfilled, parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, noteIds, scenario } from "./todo.ts";

export const stateCreatedNote = scenario({
  description:
    "Add a task, which creates a note, and expect in Then that noteIds answers with a key written in the form of a key that todo creates, so check reports writtenCreatedKey at the expectation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [], Note: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    return { noting: w.client.call(noteIds, {}) };
  },
  then: ({ noting }) => [answered(noting, fulfilled({ noteIds: ["todo/Note-1"] }))],
});
