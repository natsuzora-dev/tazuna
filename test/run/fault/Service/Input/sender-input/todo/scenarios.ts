import { run } from "@natsuzora-dev/tazuna";
import { notes } from "../notes/contract.ts";
import { addTask, scenario } from "./todo.ts";

const given = { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: { notes: run(notes, {}) } } as const;

export const emptyTitle = scenario(
  "Add a task with an empty title; noteAdded sends addNote with the empty text, which only notes parses: its input schema does not take it, so notes rejects it with invalid-input, and test reports inputSchema of noteAdded, the sender",
  {
    given,
    when: (w) => {
      const added = w.client.send(addTask, { taskId: "task-1", title: "" });
      const note = w.net.deliver(added.request(notes.addNote));
      w.net.deliver(note.answer(note));
    },
    then: () => [],
  },
);

export const paddedTitle = scenario(
  "Add a task whose title is one space; noteAdded sends addNote with the text as written, and only notes parses it: one character passes min(1) before trim, but the trimmed empty text fails min(1) when notes encodes it again, so test reports an exception of addNote, whose schema cannot write what it parsed",
  {
    given,
    when: (w) => {
      const added = w.client.send(addTask, { taskId: "task-1", title: " " });
      const note = w.net.deliver(added.request(notes.addNote));
      w.net.deliver(note.answer(note));
    },
    then: () => [],
  },
);
