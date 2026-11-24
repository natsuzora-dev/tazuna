import type { z } from "zod";
import type { Malformed } from "../data/malformed.ts";
import { schemaNode } from "../data/schemaNode.ts";
import type { Definition, Named } from "../dsl/definition.ts";
import { keyFieldsOf, selfRefKeyFields } from "../dsl/entity.ts";
import type { Found } from "./found.ts";

/** Whether `schema` accepts null, or undefined in place of a value. */
const nullable = (schema: z.ZodType): boolean =>
  schema.safeParse(null).success || schemaNode(schema).type === "optional";

/** The keyed entities whose key lists a field twice, a field that accepts null or undefined, or a `ref.self()` field. */
export function malformedKeys(definitions: readonly Named<Definition>[]): Found<Malformed>[] {
  return definitions.flatMap(({ service, name, place, definition: d }): Found<Malformed>[] => {
    if (d.kind !== "entity" || d.single) return [];
    const fields = keyFieldsOf(d);
    const selfRefs = selfRefKeyFields(d);
    const found = (
      kind: "Malformed.repeatedKeyField" | "Malformed.nullableKeyField" | "Malformed.selfRefKeyField",
      field: string,
    ) => ({
      violation: { kind, definition: { service, name }, data: { field } },
      place,
    });
    return [
      ...fields.filter((f, i) => fields.indexOf(f) !== i).map((f) => found("Malformed.repeatedKeyField", f)),
      ...fields
        .filter((f, i) => fields.indexOf(f) === i && !selfRefs.includes(f) && nullable(d.fields[f] as z.ZodType))
        .map((f) => found("Malformed.nullableKeyField", f)),
      ...selfRefs.filter((f, i) => selfRefs.indexOf(f) === i).map((f) => found("Malformed.selfRefKeyField", f)),
    ];
  });
}
