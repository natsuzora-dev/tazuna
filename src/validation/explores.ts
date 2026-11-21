import type { Illegal } from "../data/illegal.generated.ts";
import { domainOf, moveSchemas, rootTree } from "../spec/domains.ts";
import type { Structure } from "../spec/structure.generated.ts";
import { type ExploreStructure, schemaOwner } from "../spec/structure.ts";

/** Lean's Explores.undeclared. */
const undeclared = (structure: Structure, x: ExploreStructure): Illegal[] =>
  moveSchemas(structure, x.service).flatMap(([schema, json]) => {
    const tree = rootTree(domainOf(x.domains, schema), json);
    return tree.ok
      ? []
      : tree.undeclared.map(
          (path): Illegal => ({
            kind: "Illegal.undeclaredDomain",
            definition: schemaOwner(schema),
            data: { service: x.service, schema, path: [...path] },
          }),
        );
  });

/** Lean's Explores.check. */
export const check = (structure: Structure): Illegal[] => structure.explores.flatMap((x) => undeclared(structure, x));
