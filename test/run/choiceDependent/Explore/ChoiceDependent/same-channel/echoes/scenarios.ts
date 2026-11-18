import { arm, scenario } from "./echoes.ts";

export const echoTie = scenario(
  "Arm at 09:00 and move the clock to 10:30; the deadlines of first and second tie at 10:00, and echoed is caused by the rang that hearer hears first, so the tie's order shows in which rang echoed follows: stepOrder",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.client.send(arm, {});
      w.clock.at("2026-10-25T10:30:00+09:00");
    },
    then: () => [],
  },
);
