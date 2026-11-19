import { accepted, external } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { given, scenario } from "./app.ts";

const arranged = given({ start: "2026-10-25T10:00:00+09:00", records: {}, peers: [external(device)] });

export const firstRestart = scenario({
  description:
    "Restart as the first line; the service began at the start of Given, and begins again on the restart, so permission sends a second requestPermission, after the restart line",
  given: arranged,
  when: (w) => {
    const restarting = w.host.restart();
    const first = w.startup.request(device.requestPermission);
    w.net.deliver(first);
    w.peer.device.leaveUnanswered(first);
    const second = restarting.request(device.requestPermission);
    w.net.deliver(second);
    w.peer.device.leaveUnanswered(second);
  },
  then: () => [],
});

export const requestsDiscarded = scenario({
  description:
    "Begin at 10:00, restart at 10:05, and answer requestPermission; the restart discards the request of the first start, so the answer goes to the request of the new start",
  given: arranged,
  when: (w) => {
    const first = w.startup.request(device.requestPermission);
    w.net.deliver(first);
    w.peer.device.leaveUnanswered(first);
    w.clock.at("2026-10-25T10:05:00+09:00");
    const second = w.host.restart().request(device.requestPermission);
    w.net.deliver(second);
    w.net.deliver(w.peer.device.answer(second, accepted));
  },
  then: () => [],
});

export const resultAfterRestart = scenario({
  description:
    "Restart while the device holds requestPermission, then the device accepts it and emits granted as its result; the answer arrived, so the event is the result of that request, though the request of the stopped process waits no more",
  given: arranged,
  when: (w) => {
    const first = w.startup.request(device.requestPermission);
    w.net.deliver(first);
    const restarting = w.host.restart();
    w.net.leaveInFlight(restarting.request(device.requestPermission));
    w.net.deliver(w.peer.device.answer(first, accepted));
    w.net.deliver(w.peer.device.emit(device.granted, {}, { resultOf: first }));
  },
  then: () => [],
});
