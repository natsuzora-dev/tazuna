import type { Illegal } from "../data/illegal.generated.ts";
import type { Structure } from "../syntax/structure.generated.ts";

export function check(structure: Structure): Illegal[] {
  return structure.contracts.flatMap((c) =>
    Object.entries(c.members).flatMap(([key, member]): Illegal[] =>
      member === null || member.service === c.service
        ? []
        : [{ kind: "Illegal.foreignMember", definition: null, data: { contract: c.service, key } }],
    ),
  );
}
