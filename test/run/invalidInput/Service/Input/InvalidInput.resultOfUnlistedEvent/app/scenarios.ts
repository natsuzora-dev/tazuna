import { accepted, external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const denyUnlisted = scenario({
  description:
    "Link denied to the accepted request, whose command does not emit denied; test reports resultOfUnlistedEvent when the run ends",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(device)] },
  when: (w) => {
    w.net.deliver(w.startup.request(device.requestPermission));
    w.net.deliver(w.peer.device.answer(w.startup.request(device.requestPermission), accepted()));
    w.net.deliver(w.peer.device.emit(device.denied, {}, { resultOf: w.startup.request(device.requestPermission) }));
  },
  then: () => [],
});
