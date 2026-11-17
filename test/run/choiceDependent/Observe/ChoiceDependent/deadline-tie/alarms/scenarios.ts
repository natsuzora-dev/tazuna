import { arm, scenario } from "./alarms.ts";

export const armLate = scenario(
  "Arm at 11:00; the deadlines of first and second are both 10:00, which has passed, so they tie when alarms finishes processing arm. No line orders that tie, and the clock that rings last decides the alarm, so test reports stepOrder",
  {
    given: { start: "2026-10-25T11:00:00+09:00", records: { Alarm: { by: "" } }, peers: {} },
    when: (w) => {
      w.client.send(arm, {});
    },
    then: () => [],
  },
);
