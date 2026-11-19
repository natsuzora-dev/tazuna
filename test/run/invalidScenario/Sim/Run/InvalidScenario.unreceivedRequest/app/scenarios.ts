import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const grantUndelivered = scenario({
  description: "The device emits granted as the result of requestPermission, which no line delivered to it",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(device)] },
  when: (w) => {
    w.net.leaveInFlight(w.startup.request(device.requestPermission));
    w.peer.device.emit(device.granted, {}, { resultOf: w.startup.request(device.requestPermission) });
  },
  then: () => [],
});
