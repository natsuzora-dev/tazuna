import { run } from "@natsuzora-dev/tazuna";
import { notes } from "../notes/contract.ts";
import { addTask, given, scenario } from "./todo.ts";

const arranged = given({ start: "2026-10-25T09:00:00+09:00", records: {}, peers: [run(notes, {})] });

export const paddedText = scenario({
  description:
    "Add a task whose title has spaces around it; noteAdded sends addNote with the text as todo wrote it, so the in line of notes keeps the spaces and only notes's parse trims them",
  given: arranged,
  when: (w) => {
    const added = w.client.send(addTask, { title: " x " });
    const note = w.net.deliver(added.request(notes.addNote));
    w.net.deliver(note.answer(note));
  },
  then: () => [],
});
