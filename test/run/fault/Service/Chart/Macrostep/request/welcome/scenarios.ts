import { join, scenario } from "./welcome.ts";

export const joinNameless = scenario(
  "Join with an empty nickname; greetJoined sends greet with the empty nickname, which fails the input schema of greet, so test reports automationInputSchema",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.client.send(join, { nickname: "" });
    },
    then: () => [],
  },
);
