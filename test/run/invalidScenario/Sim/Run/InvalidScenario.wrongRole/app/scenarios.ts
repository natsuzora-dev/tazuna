import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const deviceRequestsItself = scenario({
  description:
    "Leave requestPermission in flight, and the device sends requestPermission, a command of its own, which only a running service receives",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(device)] },
  when: (w) => {
    w.net.leaveInFlight(w.startup.request(device.requestPermission));
    w.peer.device.send(device.requestPermission, {});
  },
  then: () => [],
});
