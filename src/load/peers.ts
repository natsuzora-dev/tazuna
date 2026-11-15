import type { Malformed } from "../data/malformed.ts";
import type { Contract, Named, Place, ServiceDefinition } from "../dsl/definition.ts";
import type { Scenario } from "../dsl/scenario.ts";
import type { Found } from "./found.ts";

/**
 * Returns the services that a scenario's `given` or `elsewhere` names and that are not other services of the spec that
 * are not external (Malformed.unknownPeer), the given states that are not states of their service's contract
 * (Malformed.unlistedState), and the given states and elsewhere inputs that give a peer an event of the scenario's own
 * service (Malformed.ownEventToPeer). `elsewhere` names the service of the exported contract that it gives, and no
 * service for another object.
 */
export function peerReferences(
  scenarios: readonly Named<Scenario>[],
  services: ReadonlyMap<string, { readonly definition: ServiceDefinition; readonly place: Place }>,
  contracts: readonly Contract[],
): Found<Malformed>[] {
  return scenarios.flatMap(({ service, name, place, definition }) => {
    const scenario = { service, name };
    const isPeer = (peer: string | null): peer is string =>
      peer !== null && peer !== service && services.get(peer)?.definition.external === false;
    const own = new Set(contracts.filter((c) => c.service === service).flatMap((c) => Object.values(c.members)));
    const isOwnEvent = (input: { readonly type: string; readonly event?: unknown }) =>
      input.type === "event" && own.has(input.event);
    const ownEventToPeer = (peer: string, input?: number): Found<Malformed> => ({
      violation: {
        kind: "Malformed.ownEventToPeer",
        definition: null,
        scenario,
        ...(input === undefined ? {} : { input }),
        data: { service: peer },
      },
      place,
    });
    const unknownPeer = (peer: string | null, input?: number): Found<Malformed> => ({
      violation: {
        kind: "Malformed.unknownPeer",
        definition: null,
        scenario,
        ...(input === undefined ? {} : { input }),
        data: { service: peer },
      },
      place,
    });
    return [
      ...Object.entries(definition.given).flatMap(([peer, state]): Found<Malformed>[] => {
        if (!isPeer(peer)) return [unknownPeer(peer)];
        const states = contracts.filter((c) => c.service === peer).flatMap((c) => Object.values(c.states));
        if (states.includes(state)) return state.some(isOwnEvent) ? [ownEventToPeer(peer)] : [];
        return [
          {
            violation: { kind: "Malformed.unlistedState", definition: null, scenario, data: { service: peer } },
            place,
          },
        ];
      }),
      ...definition.inputs.flatMap((input, i): Found<Malformed>[] => {
        if (input.type !== "elsewhere") return [];
        const peer = contracts.find((c) => c.value === input.service)?.service ?? null;
        if (!isPeer(peer)) return [unknownPeer(peer, i + 1)];
        return isOwnEvent(input.input) ? [ownEventToPeer(peer, i + 1)] : [];
      }),
    ];
  });
}
