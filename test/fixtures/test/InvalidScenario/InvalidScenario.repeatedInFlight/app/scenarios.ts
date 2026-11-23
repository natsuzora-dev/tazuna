import { external, parseInstant } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const leaveTwice = scenario({
  description: "Leave requestPermission in flight twice",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(device)] },
  when: (w) => {
    w.net.leaveInFlight(w.startup.request(device.requestPermission));
    w.net.leaveInFlight(w.startup.request(device.requestPermission));
  },
  then: () => [],
});
