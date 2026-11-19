import { accepted, external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { ask, scenario, status } from "./app.ts";

export const answerAfterRestart = scenario(
  "Press ask, restart, and answer requestPermission; the restart discards the request, and permission starts again in idle, so the answer reaches no waiting request and changes nothing; no violation",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { device: external(device) } },
    when: (w) => {
      const asking = w.client.send(ask, {}).request(device.requestPermission);
      w.host.restart();
      w.net.deliver(asking);
      w.net.deliver(w.peer.device.answer(asking, accepted));
    },
    then: () => [],
  },
);

export const unsubscribeAfterRestart = scenario(
  "Subscribe to status, restart, and end the subscription; the restart drops the subscription, so test reports unopenedSubscription",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { device: external(device) } },
    when: (w) => {
      const watching = w.client.subscribe(status, {});
      w.host.restart();
      w.client.unsubscribe(watching);
    },
    then: () => [],
  },
);
