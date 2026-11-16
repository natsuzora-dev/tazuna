import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const grantAfterRetry = scenario(
  "Link results to a rejected request and to a request that cannot have them; test reports resultOfUnacceptedRequest and resultOfUnlistedEvent",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { device: external(device) } },
    when: (w) => {
      w.net.deliver(w.begin.request(device.requestPermission));
      const retried = w.net.deliver(
        w.peer.device.answer(w.begin.request(device.requestPermission), {
          result: "rejected",
          rejection: { kind: "unavailable" },
        }),
      );
      w.net.deliver(w.peer.device.emit(device.granted, {}, { resultOf: w.begin.request(device.requestPermission) }));
      w.net.deliver(retried.request(device.requestPermission));
      w.net.deliver(w.peer.device.answer(retried.request(device.requestPermission), { result: "accepted" }));
      w.net.deliver(w.peer.device.emit(device.denied, {}, { resultOf: retried.request(device.requestPermission) }));
    },
    then: () => [],
  },
);
