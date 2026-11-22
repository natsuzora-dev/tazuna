import { accepted, external, parseInstant } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { given, scenario } from "./app.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [external(device)] });

export const resultAfterRestart = scenario({
  description:
    "Restart while the device holds requestPermission, then the device accepts it and emits granted as its result; the answer arrived, so the event is the result of that request, though the request of the stopped process waits no more",
  given: arranged,
  when: (w) => {
    const first = w.startup.request(device.requestPermission);
    w.net.deliver(first);
    const restarting = w.host.restart();
    w.net.leaveInFlight(restarting.request(device.requestPermission));
    w.net.deliver(w.peer.device.answer(first, accepted()));
    w.net.deliver(w.peer.device.emit(device.granted, {}, { resultOf: first }));
  },
  then: () => [],
});
