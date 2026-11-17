import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const grant = scenario(
  "Accept the permission request and receive granted with its resultOf; device accepts the requestPermission that permission sends and emits the result event granted. The granted line of the snapshot has the id of the requestPermission request in resultOf",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { device: external(device) } },
    when: (w) => {
      const request = w.startup.request(device.requestPermission);
      w.net.deliver(request);
      w.net.deliver(w.peer.device.answer(request, { result: "accepted" }));
      w.net.deliver(w.peer.device.emit(device.granted, {}, { resultOf: request }));
    },
    then: () => [],
  },
);
