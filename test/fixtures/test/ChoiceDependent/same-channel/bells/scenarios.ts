import { external, parseInstant } from "@natsuzora-dev/tazuna";
import { pager } from "../pager/contract.ts";
import { arm, scenario } from "./bells.ts";

export const ringTie = scenario({
  description:
    "Arm at 09:00 and move the clock to 10:30; the deadlines of first and second tie at 10:00, and each clock emits rang on the one channel of bells' events, but no cause chain links the two steps, so the rang events keep no order and nothing is reported",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(pager)] },
  when: (w) => {
    w.client.as("client").send(arm, {});
    const tick = w.clock.at(parseInstant("2026-10-25T10:30:00+09:00"));
    w.net.leaveInFlight(tick.request(pager.page, { by: "first" }));
    w.net.leaveInFlight(tick.request(pager.page, { by: "second" }));
  },
  then: () => [],
});
