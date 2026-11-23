import type { z } from "zod";
import { markOf } from "../../data/marks.ts";
import type { Restricted, schemaFeatures } from "../../data/restricted.ts";
import { constantMessage, isDecimal, schemaNode } from "../../data/schemaNode.ts";
import { isSelfRef } from "../../dsl/entity.ts";
import type { Found } from "../../load/found.ts";
import type { LoadedSpec } from "../../load/load.ts";
import { definitionSchemas, type SchemaAt, schemasIn } from "../../load/schemas.ts";

type Feature = (typeof schemaFeatures)[number];

/** The string formats that Lean checks as Zod does. */
const leanFormats = new Set(["starts_with", "ends_with", "includes", "date"]);

/** The checks that Zod runs on `schema`, the schema itself first when it is a check, as z.email() is. */
const checksOn = (schema: z.ZodType): readonly z.core.$ZodCheck[] => [
  ...(schema._zod.traits.has("$ZodCheck") ? [schema as unknown as z.core.$ZodCheck] : []),
  ...(schema._zod.def.checks ?? []),
];

function checkFeature(check: z.core.$ZodCheck): Feature | undefined {
  if (markOf(check as z.core.$ZodCheck<never>) !== undefined) return undefined;
  const def = check._zod.def as unknown as Readonly<Record<string, unknown>>;
  if (def["check"] === "custom") return "refinement";
  if (def["check"] === "overwrite") return "overwrite";
  if (def["check"] === "string_format" && !(leanFormats.has(String(def["format"])) && def["position"] === undefined))
    return "stringFormat";
  return def["error"] !== undefined && constantMessage(def["error"]) === undefined ? "message" : undefined;
}

/** The feature of a schema that the walk does not enter, since the schemas inside it are its own. */
function wrapping(schema: z.ZodType): Feature | undefined {
  const node = schemaNode(schema);
  if (node.type === "codec" || node.type === "pipe" || (node.type === "opaque" && node.kind === "transform"))
    return "codec";
  return node.type === "lazy" && !isSelfRef(schema) ? "recursion" : undefined;
}

/** The features of `schema` itself that Lean cannot parse, not those of the schemas inside it. */
function featuresOf(schema: z.ZodType): Feature[] {
  const node = schemaNode(schema);
  const def = schema._zod.def as { readonly error?: unknown; readonly coerce?: unknown };
  const own: Feature[] = [
    ...(node.type === "record" || node.type === "tuple" ? [node.type] : [wrapping(schema) ?? []].flat()),
    ...(def.coerce === true ? (["overwrite"] as const) : []),
    ...(isDecimal(schema) ? (["decimal"] as const) : []),
    ...(def.error !== undefined && constantMessage(def.error) === undefined ? (["message"] as const) : []),
  ];
  return [...new Set([...own, ...checksOn(schema).flatMap((c) => checkFeature(c) ?? [])])];
}

const stop = (schema: z.ZodType) => wrapping(schema) !== undefined;

const restrictedIn = (schemas: readonly SchemaAt[]) =>
  schemas.flatMap(({ path, schema }) => featuresOf(schema).map((feature) => ({ path, feature })));

export function check(spec: LoadedSpec): Found<Restricted>[] {
  return [
    ...spec.definitions.flatMap(({ service, name, place, definition }) =>
      restrictedIn(definitionSchemas(definition, stop)).map(
        (data): Found<Restricted> => ({
          violation: { kind: "Restricted.schema", definition: { service, name }, data },
          place,
        }),
      ),
    ),
    ...spec.constants.flatMap(({ name, place, definition }) =>
      restrictedIn(schemasIn(definition.schema, [], stop)).map(
        (data): Found<Restricted> => ({
          violation: { kind: "Restricted.schema", definition: null, data: { name, ...data } },
          place,
        }),
      ),
    ),
  ];
}
