import { accepted, external, parseInstant } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const answerUndelivered = scenario({
  description: "The device answers requestPermission, which no line delivered",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(device)] },
  when: (w) => {
    w.net.deliver(w.peer.device.answer(w.startup.request(device.requestPermission), accepted()));
  },
  then: () => [],
});
