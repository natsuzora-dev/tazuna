import { go, scenario } from "./door.ts";

export const both = scenario(
  "next and stop unordered; both orders end in idle, the same in every way a later input reads",
  {
    given: { start: "2026-10-25T09:00:00Z", records: { Door: { used: false } }, peers: {} },
    when: (w) => {
      w.client.send(go, { ks: ["next", "stop"] });
    },
    then: () => [],
  },
);
