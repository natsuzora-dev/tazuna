import type { Illegal } from "../data/illegal.generated.ts";
import type { Structure } from "../syntax/structure.generated.ts";

export function check(structure: Structure): Illegal[] {
  return structure.definitions.flatMap((d): Illegal[] =>
    d.kind !== "command"
      ? []
      : d.emits.flatMap((e): Illegal[] =>
          e === null || e.service === d.service
            ? []
            : [{ kind: "Illegal.foreignEvent", definition: { service: d.service, name: d.name }, data: { event: e } }],
        ),
  );
}
