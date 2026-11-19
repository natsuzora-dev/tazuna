import { run } from "@natsuzora-dev/tazuna";
import { notes } from "../notes/contract.ts";
import { addTask, scenario } from "./todo.ts";

const given = { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [run(notes, {})] } as const;

export const emptyTitleAfterRestart = scenario(
  "As sender-input's emptyTitle, but todo restarts before notes' invalid-input rejection arrives, so nothing waits for it: the end of the run checks every answer that arrived, and test reports inputSchema of noteAdded, the sender",
  {
    given,
    when: (w) => {
      const added = w.client.send(addTask, { taskId: "task-1", title: "" });
      const note = w.net.deliver(added.request(notes.addNote));
      const answer = note.answer(note);
      w.host.restart();
      w.net.deliver(answer);
    },
    then: () => [],
  },
);
