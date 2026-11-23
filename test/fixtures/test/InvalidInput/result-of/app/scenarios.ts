import { accepted, external, parseInstant, rejected } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { scenario } from "./app.ts";

export const grantRejected = scenario({
  description:
    "Link granted to a request that the device rejected; test reports resultOfUnacceptedRequest when the run ends, since the event cannot be that request's result",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(device)] },
  when: (w) => {
    w.net.deliver(w.startup.request(device.requestPermission));
    w.net.deliver(w.peer.device.answer(w.startup.request(device.requestPermission), rejected("unavailable")));
    w.net.deliver(w.peer.device.emit(device.granted, {}, { resultOf: w.startup.request(device.requestPermission) }));
  },
  then: () => [],
});

export const denyUnlisted = scenario({
  description:
    "Link denied to the accepted request, whose command does not emit denied; test reports resultOfUnlistedEvent when the run ends",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(device)] },
  when: (w) => {
    w.net.deliver(w.startup.request(device.requestPermission));
    w.net.deliver(w.peer.device.answer(w.startup.request(device.requestPermission), accepted()));
    w.net.deliver(w.peer.device.emit(device.denied, {}, { resultOf: w.startup.request(device.requestPermission) }));
  },
  then: () => [],
});

export const grantBeforeAnswer = scenario({
  description:
    "The device emits granted as the result of the permission request before app takes its answer; a result event may arrive before or after the answer, as a Stripe webhook may arrive before the API response. permission waits in asking, which takes no granted, so the event changes nothing; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(device)] },
  when: (w) => {
    const request = w.startup.request(device.requestPermission);
    w.net.deliver(request);
    const answer = w.peer.device.answer(request, accepted());
    w.net.deliver(w.peer.device.emit(device.granted, {}, { resultOf: request }));
    w.net.deliver(answer);
  },
  then: () => [],
});

export const grantAfterAnswer = scenario({
  description:
    "The device accepts the permission request and then emits granted as its result; permission is allowed; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(device)] },
  when: (w) => {
    const request = w.startup.request(device.requestPermission);
    w.net.deliver(request);
    w.net.deliver(w.peer.device.answer(request, accepted()));
    w.net.deliver(w.peer.device.emit(device.granted, {}, { resultOf: request }));
  },
  then: () => [],
});

export const grantBeforeRejection = scenario({
  description:
    "The device emits granted as the result of the permission request and then rejects the request; the end of the run checks the event against the answer that came later, and test reports resultOfUnacceptedRequest",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(device)] },
  when: (w) => {
    const request = w.startup.request(device.requestPermission);
    w.net.deliver(request);
    const rejection = w.peer.device.answer(request, rejected("unavailable"));
    w.net.deliver(w.peer.device.emit(device.granted, {}, { resultOf: request }));
    const retry = w.net.deliver(rejection).request(device.requestPermission);
    w.net.deliver(retry);
    w.peer.device.leaveUnanswered(retry);
  },
  then: () => [],
});
