import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const grantRejected = scenario(
  "Link granted to a request that the device rejected; test reports resultOfUnacceptedRequest and halts, since the event cannot be that request's result",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { device: external(device) } },
    when: (w) => {
      w.net.deliver(w.startup.request(device.requestPermission));
      w.net.deliver(
        w.peer.device.answer(w.startup.request(device.requestPermission), {
          result: "rejected",
          rejection: { kind: "unavailable" },
        }),
      );
      w.net.deliver(w.peer.device.emit(device.granted, {}, { resultOf: w.startup.request(device.requestPermission) }));
    },
    then: () => [],
  },
);

export const denyUnlisted = scenario(
  "Link denied to the accepted request, whose command does not emit denied; test reports resultOfUnlistedEvent and halts",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { device: external(device) } },
    when: (w) => {
      w.net.deliver(w.startup.request(device.requestPermission));
      w.net.deliver(w.peer.device.answer(w.startup.request(device.requestPermission), { result: "accepted" }));
      w.net.deliver(w.peer.device.emit(device.denied, {}, { resultOf: w.startup.request(device.requestPermission) }));
    },
    then: () => [],
  },
);
