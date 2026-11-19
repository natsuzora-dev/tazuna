import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const deliverUnsent = scenario({
  description:
    "Leave requestPermission in flight, advance the clock, and deliver a requestPermission that the clock line sent, which it did not",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(device)] },
  when: (w) => {
    w.net.leaveInFlight(w.startup.request(device.requestPermission));
    const later = w.clock.at("2026-10-25T10:00:00+09:00");
    w.net.deliver(later.request(device.requestPermission));
  },
  then: () => [],
});
