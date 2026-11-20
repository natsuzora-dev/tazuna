import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { Found } from "../../load/found.ts";
import type { LoadedSpec } from "../../load/load.ts";

export const check = (spec: LoadedSpec): Found<NonCanonical>[] => [
  ...[...spec.services]
    .filter(([, s]) => s.definition.description === "")
    .map(
      ([service, s]): Found<NonCanonical> => ({
        violation: { kind: "NonCanonical.undescribedService", definition: null, data: { service } },
        place: s.place,
      }),
    ),
  ...spec.definitions.flatMap((d): Found<NonCanonical>[] =>
    "description" in d.definition && d.definition.description === ""
      ? [
          {
            violation: {
              kind: "NonCanonical.undescribedDefinition",
              definition: { service: d.service, name: d.name },
              data: {},
            },
            place: d.place,
          },
        ]
      : [],
  ),
];
