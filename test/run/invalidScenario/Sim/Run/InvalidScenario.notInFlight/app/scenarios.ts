import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const deliverTwice = scenario({
  description: "The network delivers requestPermission twice",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(device)] },
  when: (w) => {
    w.net.deliver(w.startup.request(device.requestPermission));
    w.net.deliver(w.startup.request(device.requestPermission));
  },
  then: () => [],
});
