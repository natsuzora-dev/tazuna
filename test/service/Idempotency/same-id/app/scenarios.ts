import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const resultRedelivered = scenario(
  "Accept the permission request and receive device.granted twice with the same id and the same resultOf; app writes the second as a line with resultOf and does not process it",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { device: external(device) } },
    when: (w) => {
      const request = w.begin.request(device.requestPermission);
      w.net.deliver(request);
      w.net.deliver(w.peer.device.answer(request, { result: "accepted" }));
      const granted = w.peer.device.emit(device.granted, {}, { resultOf: request });
      w.net.deliver(granted);
      w.net.redeliver(granted);
    },
    then: () => [],
  },
);
