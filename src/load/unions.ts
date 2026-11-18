import type { z } from "zod";
import type { Malformed } from "../data/malformed.ts";
import { holdsCodec, schemaNode } from "../data/schemaNode.ts";
import type { Definition, Named } from "../dsl/definition.ts";
import type { Found } from "./found.ts";
import { definitionSchemas, type SchemaAt, schemasIn } from "./schemas.ts";

function isUndiscriminated(schema: z.ZodType): boolean {
  const node = schemaNode(schema);
  return node.type === "union" && node.discriminator === undefined && node.options.some((o) => holdsCodec(o));
}

/** The undiscriminated unions among `schemas`; a walk that stops at isUndiscriminated leaves only the outermost. */
const undiscriminatedIn = (schemas: readonly SchemaAt[]) =>
  schemas.filter(({ schema }) => isUndiscriminated(schema)).map(({ path }) => ({ path }));

export function undiscriminatedUnions(
  definitions: readonly Named<Definition>[],
  constants: readonly Named<{ readonly schema: z.ZodObject }>[],
): Found<Malformed>[] {
  return [
    ...definitions.flatMap(({ service, name, place, definition }) =>
      undiscriminatedIn(definitionSchemas(definition, isUndiscriminated)).map(
        (data): Found<Malformed> => ({
          violation: { kind: "Malformed.undiscriminatedUnion", definition: { service, name }, data },
          place,
        }),
      ),
    ),
    ...constants.flatMap(({ name, place, definition }) =>
      undiscriminatedIn(schemasIn(definition.schema, [], isUndiscriminated)).map(
        (data): Found<Malformed> => ({
          violation: { kind: "Malformed.undiscriminatedUnion", definition: null, data: { name, ...data } },
          place,
        }),
      ),
    ),
  ];
}
