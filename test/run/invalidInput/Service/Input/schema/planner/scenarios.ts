import { external, rejected, type When } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./planner.ts";

const given = { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(todo)] } as const;

const answered = (w: When<typeof given.peers>, answer: Parameters<typeof w.peer.todo.answer>[1]) => {
  const adding = w.startup.request(todo.addTask);
  w.net.deliver(adding);
  w.net.deliver(w.peer.todo.answer(adding, answer));
};

export const rejectAdd = scenario("Reject the task as already existing; no violation", {
  given,
  when: (w) => answered(w, rejected("already-exists")),
  then: () => [],
});

export const rejectAddNotFound = scenario(
  "Reject the task as not-found although its input has no ref; addTask cannot answer with that kind, so test reports unlistedRejectionKind",
  {
    given,
    when: (w) => answered(w, rejected("not-found")),
    then: () => [],
  },
);

export const rejectMetRequires = scenario(
  "Reject the task for the requires short, which its title meets, so test reports rejectedAssumedRequires",
  {
    given,
    when: (w) => answered(w, rejected("requires", "short")),
    then: () => [],
  },
);
