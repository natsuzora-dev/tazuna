import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const grantBeforeAnswer = scenario(
  "The device emits granted as the result of the permission request before app takes its answer, so app cannot tell which request the event belongs to; test reports resultOfUnansweredRequest",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: { device: external(device) } },
    when: (w) => {
      const request = w.startup.request(device.requestPermission);
      w.net.deliver(request);
      w.net.deliver(w.peer.device.emit(device.granted, {}, { resultOf: request }));
    },
    then: () => [],
  },
);
