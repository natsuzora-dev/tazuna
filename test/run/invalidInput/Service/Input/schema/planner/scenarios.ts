import { external, type When } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./planner.ts";

const given = { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { todo: external(todo) } } as const;

const answered = (w: When<typeof given.peers>, answer: Parameters<typeof w.peer.todo.answer>[1]) => {
  const adding = w.begin.request(todo.addTask);
  w.net.deliver(adding);
  w.net.deliver(w.peer.todo.answer(adding, answer));
};

export const rejectAdd = scenario("Reject the task as already existing; no violation", {
  given,
  when: (w) => answered(w, { result: "rejected", rejection: { kind: "already-exists" } }),
  then: () => [],
});

export const rejectAddNotFound = scenario(
  "Reject the task as not-found although its input has no ref; addTask cannot answer with that kind, so test reports unlistedRejectionKind",
  {
    given,
    when: (w) => answered(w, { result: "rejected", rejection: { kind: "not-found" } }),
    then: () => [],
  },
);

export const rejectUnknownReason = scenario(
  "Reject the task with the reason long; long is not a requires of addTask, so test reports unlistedRejectionReason, and the title meets the assumed requires short, so it also reports rejectedAssumedRequires",
  {
    given,
    when: (w) => answered(w, { result: "rejected", rejection: { kind: "requires", reason: "long" } }),
    then: () => [],
  },
);
