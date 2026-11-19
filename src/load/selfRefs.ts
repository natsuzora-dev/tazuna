import type { z } from "zod";
import type { Malformed } from "../data/malformed.ts";
import type { Definition, Named } from "../dsl/definition.ts";
import { misplacedSelfRef } from "../dsl/entity.ts";
import type { Found } from "./found.ts";
import { definitionSchemas, type SchemaAt, schemasIn } from "./schemas.ts";

const misplacedIn = (schemas: readonly SchemaAt[]) =>
  schemas.flatMap(({ path, schema }) => (misplacedSelfRef(schema) ? [{ path }] : []));

export function misplacedSelfRefs(
  definitions: readonly Named<Definition>[],
  constants: readonly Named<{ readonly schema: z.ZodObject }>[],
): Found<Malformed>[] {
  return [
    ...definitions.flatMap(({ service, name, place, definition }) =>
      misplacedIn(definitionSchemas(definition, misplacedSelfRef)).map(
        (data): Found<Malformed> => ({
          violation: { kind: "Malformed.misplacedSelfRef", definition: { service, name }, data },
          place,
        }),
      ),
    ),
    ...constants.flatMap(({ name, place, definition }) =>
      misplacedIn(schemasIn(definition.schema, [], misplacedSelfRef)).map(
        (data): Found<Malformed> => ({
          violation: { kind: "Malformed.misplacedSelfRef", definition: null, data: { name, ...data } },
          place,
        }),
      ),
    ),
  ];
}
