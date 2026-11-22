import { parseInstant, run } from "@natsuzora-dev/tazuna";
import { notes } from "../notes/contract.ts";
import { addTask, given, scenario } from "./todo.ts";

const arranged = given({
  start: parseInstant("2026-10-25T09:00:00+09:00"),
  records: { Task: [] },
  peers: [run(notes, {})],
});

export const emptyTitle = scenario({
  description:
    "Add a task with an empty title; noteAdded sends addNote with the empty text, which only notes parses: its input schema does not take it, so notes rejects it with invalid-input, and test reports inputSchema of noteAdded, the sender",
  given: arranged,
  when: (w) => {
    const added = w.client.send(addTask, { taskId: "task-1", title: "" });
    const note = w.net.deliver(added.request(notes.addNote));
    w.net.deliver(note.answer(note));
  },
  then: () => [],
});

export const paddedTitle = scenario({
  description:
    "Add a task whose title is one space; noteAdded sends addNote with the text as written, and only notes parses it: one character passes min(1) before trim, and notes records the trimmed empty text in noteKept without checking it again; no violation",
  given: arranged,
  when: (w) => {
    const added = w.client.send(addTask, { taskId: "task-1", title: " " });
    const note = w.net.deliver(added.request(notes.addNote));
    w.net.deliver(note.answer(note));
  },
  then: () => [],
});
