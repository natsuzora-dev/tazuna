import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const emitMuted = scenario({
  description: "Leave requestPermission in flight, and the device emits muted, which app does not receive",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(device)] },
  when: (w) => {
    w.net.leaveInFlight(w.startup.request(device.requestPermission));
    w.peer.device.emit(device.muted, {}, { resultOf: null });
  },
  then: () => [],
});
