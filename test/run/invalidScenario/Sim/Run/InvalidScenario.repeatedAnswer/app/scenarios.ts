import { accepted, external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const answerTwice = scenario({
  description: "The device answers requestPermission twice",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(device)] },
  when: (w) => {
    const request = w.net.deliver(w.startup.request(device.requestPermission));
    w.net.deliver(w.peer.device.answer(request, accepted()));
    w.peer.device.answer(request, accepted());
  },
  then: () => [],
});
