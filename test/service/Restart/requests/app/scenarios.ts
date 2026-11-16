import { external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { device: external(device) } } as const;

export const firstRestart = scenario(
  "Restart as the first line; the service began at the start of Given, and begins again on the restart, so permission sends a second requestPermission, after the restart line",
  {
    given,
    when: (w) => {
      w.peer.device.leaveUnanswered(w.begin.request(device.requestPermission));
      w.peer.device.leaveUnanswered(w.host.restart().request(device.requestPermission));
    },
    then: () => [],
  },
);

export const requestsDiscarded = scenario(
  "Begin at 10:00, restart at 10:05, and answer requestPermission; the restart discards the request of the first start, so the answer goes to the request of the new start",
  {
    given,
    when: (w) => {
      w.peer.device.leaveUnanswered(w.begin.request(device.requestPermission));
      w.clock.at("2026-10-25T10:05:00+09:00");
      const restarting = w.host.restart();
      w.peer.device.answer(restarting.request(device.requestPermission), { result: "accepted" });
    },
    then: () => [],
  },
);
