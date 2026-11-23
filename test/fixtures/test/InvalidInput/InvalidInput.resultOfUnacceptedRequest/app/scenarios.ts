import { external, parseInstant, rejected } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const grantRejected = scenario({
  description:
    "Link granted to a request that the device rejected; test reports resultOfUnacceptedRequest when the run ends, since the event cannot be that request's result",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(device)] },
  when: (w) => {
    w.net.deliver(w.startup.request(device.requestPermission));
    w.net.deliver(w.peer.device.answer(w.startup.request(device.requestPermission), rejected("unavailable")));
    w.net.deliver(w.peer.device.emit(device.granted, {}, { resultOf: w.startup.request(device.requestPermission) }));
  },
  then: () => [],
});
