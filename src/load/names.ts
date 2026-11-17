import type { Malformed } from "../data/malformed.ts";
import type { Place } from "../dsl/definition.ts";
import { reservedNameCharacters } from "../dsl/service.ts";
import type { Found } from "./found.ts";

export interface NamedExport {
  readonly name: string;
  readonly service: string;
  readonly place: Place;
  readonly value: unknown;
}

/**
 * Returns a duplicateName violation for a name that names two values in one service, and an alias violation for a value
 * exported under a second name. A service spans its files, as Go rejects a name declared twice across the files of a
 * package.
 */
export function duplicateNames(exports: readonly NamedExport[]): Found<Malformed>[] {
  return exports.flatMap((e, i): Found<Malformed>[] => {
    const earlier = exports.slice(0, i).filter((x) => x.service === e.service);
    const named = earlier.find((x) => x.name === e.name);
    if (named !== undefined)
      return named.value === e.value
        ? []
        : [
            {
              violation: {
                kind: "Malformed.duplicateName",
                definition: null,
                data: { name: e.name, elsewhere: named.place.file },
              },
              place: e.place,
            },
          ];
    const first = earlier.find((x) => x.value === e.value);
    return first === undefined
      ? []
      : [
          {
            violation: { kind: "Malformed.alias", definition: null, data: { name: first.name, alias: e.name } },
            place: e.place,
          },
        ];
  });
}

/** Returns a reservedNameCharacter violation for each service or scenario name with a character in reservedNameCharacters. */
export function reservedNames(named: readonly { readonly name: string; readonly place: Place }[]): Found<Malformed>[] {
  return named.flatMap(({ name, place }): Found<Malformed>[] => {
    const character = reservedNameCharacters.find((c) => name.includes(c));
    return character === undefined
      ? []
      : [
          {
            violation: { kind: "Malformed.reservedNameCharacter", definition: null, data: { name, character } },
            place,
          },
        ];
  });
}
