import type { Illegal } from "../data/illegal.generated.ts";
import type { Structure } from "../syntax/structure.generated.ts";
import { rejectionReasons } from "../syntax/structure.ts";

const foreignEvents = (structure: Structure): Illegal[] =>
  structure.definitions.flatMap((d): Illegal[] =>
    d.kind !== "command"
      ? []
      : d.emits.flatMap((e): Illegal[] =>
          e === null || e.service === d.service
            ? []
            : [{ kind: "Illegal.foreignEvent", definition: { service: d.service, name: d.name }, data: { event: e } }],
        ),
  );

/** Lean's isArrayIndex: the canonical decimal form of a whole number below 2^32 - 1. */
const isArrayIndex = (key: string): boolean => /^(0|[1-9][0-9]*)$/.test(key) && Number(key) < 2 ** 32 - 1;

const indexReasons = (structure: Structure): Illegal[] =>
  structure.definitions.flatMap((d) => {
    const definition = { service: d.service, name: d.name };
    return rejectionReasons(structure, definition)
      .filter(isArrayIndex)
      .map((reason): Illegal => ({ kind: "Illegal.indexReason", definition, data: { reason } }));
  });

export function check(structure: Structure): Illegal[] {
  return [...foreignEvents(structure), ...indexReasons(structure)];
}
