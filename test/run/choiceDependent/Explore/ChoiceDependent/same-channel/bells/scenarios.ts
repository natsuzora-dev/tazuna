import { external } from "@natsuzora-dev/tazuna";
import { pager } from "../pager/contract.ts";
import { arm, scenario } from "./bells.ts";

export const ringTie = scenario(
  "Arm at 09:00 and move the clock to 10:30; the deadlines of first and second tie at 10:00, and each clock emits rang on the one channel of bells' events, so the tie's order shows in that channel's order: stepOrder",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { pager: external(pager) } },
    when: (w) => {
      w.client.send(arm, {});
      const tick = w.clock.at("2026-10-25T10:30:00+09:00");
      w.net.leaveInFlight(tick.request(pager.page, { input: { by: "first" } }));
      w.net.leaveInFlight(tick.request(pager.page, { input: { by: "second" } }));
    },
    then: () => [],
  },
);
