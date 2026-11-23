import { type AnswerOf, external, parseInstant, rejected } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./planner.ts";

const arranged = given({ start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(todo)] });

const answered = arranged.step((w, answer: AnswerOf<typeof todo.addTask>) => {
  const adding = w.startup.request(todo.addTask);
  w.net.deliver(adding);
  w.net.deliver(w.peer.todo.answer(adding, answer));
});

export const rejectAdd = scenario({
  description: "Reject the task as already existing; no violation",
  given: arranged,
  when: (w) => answered(w, rejected("already-exists")),
  then: () => [],
});

export const rejectAddNotFound = scenario({
  description:
    "Reject the task as not-found although its input has no ref; addTask cannot answer with that kind, so test reports unlistedRejectionKind",
  given: arranged,
  when: (w) => answered(w, rejected("not-found")),
  then: () => [],
});

export const rejectMetRequires = scenario({
  description: "Reject the task for the requires short, which its title meets, so test reports rejectedAssumedRequires",
  given: arranged,
  when: (w) => answered(w, rejected("requires", "short")),
  then: () => [],
});
