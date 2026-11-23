import { accepted, external, parseInstant } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const grant = scenario({
  description:
    "Accept the permission request and receive granted with its resultOf; device accepts the requestPermission that permission sends and emits the result event granted. The granted line of the snapshot has the id of the requestPermission request in resultOf",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(device)] },
  when: (w) => {
    const request = w.startup.request(device.requestPermission);
    w.net.deliver(request);
    w.net.deliver(w.peer.device.answer(request, accepted()));
    w.net.deliver(w.peer.device.emit(device.granted, {}, { resultOf: request }));
  },
  then: () => [],
});
