import type { z } from "zod";
import { unrepresentableType } from "../data/jsonSchema.ts";
import type { Malformed } from "../data/malformed.ts";
import type { Definition, Named } from "../dsl/definition.ts";
import type { Found } from "./found.ts";
import { definitionSchemas, type SchemaAt, schemasIn } from "./schemas.ts";

const isUnrepresentable = (schema: z.ZodType) => unrepresentableType(schema) !== undefined;

/** The unrepresentable schemas among `schemas`; a walk that stops at isUnrepresentable leaves only the outermost. */
const unrepresentableIn = (schemas: readonly SchemaAt[]) =>
  schemas.flatMap(({ path, schema }) => {
    const type = unrepresentableType(schema);
    return type === undefined ? [] : [{ path, type }];
  });

export function unrepresentableSchemas(
  definitions: readonly Named<Definition>[],
  constants: readonly Named<{ readonly schema: z.ZodObject }>[],
): Found<Malformed>[] {
  return [
    ...definitions.flatMap(({ service, name, place, definition }) =>
      unrepresentableIn(definitionSchemas(definition, isUnrepresentable)).map(
        (data): Found<Malformed> => ({
          violation: { kind: "Malformed.unrepresentableSchema", definition: { service, name }, data },
          place,
        }),
      ),
    ),
    ...constants.flatMap(({ name, place, definition }) =>
      unrepresentableIn(schemasIn(definition.schema, [], isUnrepresentable)).map(
        (data): Found<Malformed> => ({
          violation: { kind: "Malformed.unrepresentableSchema", definition: null, data: { name, ...data } },
          place,
        }),
      ),
    ),
  ];
}
