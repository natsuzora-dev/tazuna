import type { Illegal } from "../data/illegal.generated.ts";
import { declared, moveSchemas, rootTree } from "../spec/domains.ts";
import type { Explore, Structure } from "../spec/structure.generated.ts";
import { schemaOwner } from "../spec/structure.ts";

/** Lean's Explores.undeclared. */
const undeclared = (structure: Structure, x: Explore): Illegal[] =>
  moveSchemas(structure, x.service).flatMap(([schema, json]) => {
    const tree = rootTree(declared(x.domains, schema), json);
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
