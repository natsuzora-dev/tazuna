import { normalizedRow } from "../data/collections.ts";
import { sameRef } from "../data/definitionRef.ts";
import type { Malformed } from "../data/malformed.ts";
import { objectOf, type Shape } from "../data/values.ts";
import { thrown, type ViolationError, zodError } from "../data/violation.ts";
import { chartOf } from "../dsl/chart.ts";
import type { Definition, Named, StateSpec } from "../dsl/definition.ts";
import type { Found } from "./found.ts";
import type { ThrownDefault } from "./structureOf.ts";

/**
 * Returns the error of the shape's defaults against the shape: Zod's issues, or what a default function or a refinement
 * threw. Zod does not validate default values itself.
 */
function defaultsError(shape: Shape): ViolationError | undefined {
  try {
    const parsed = objectOf(shape).safeParse({});
    if (!parsed.success) return zodError(parsed.error.issues);
    const checked = normalizedRow(shape, parsed.data);
    return "error" in checked ? zodError(checked.error.issues) : undefined;
  } catch (error) {
    return thrown(error);
  }
}

/** The map states among `states` and their descendants, each with its name, in document order. */
const mapStates = (
  states: Readonly<Record<string, StateSpec>>,
): (readonly [string, Extract<StateSpec, { readonly type: "map" }>])[] =>
  Object.entries(states).flatMap(([name, node]) => [
    ...(node.type === "map" ? [[name, node] as const] : []),
    ...mapStates(node.states ?? {}),
  ]);

/**
 * Returns the declared defaults that fail their schemas or throw: a single entity's fields, a map state's copy context,
 * and the schemas whose conversion in structureOf threw. A definition gets one finding for its conversions; for an
 * entity it replaces the check of the same fields. A definition that an opaqueCollection finding names is skipped: the
 * opaque collection is the cause.
 */
export function defaultSchemas(
  definitions: readonly Named<Definition>[],
  opaque: readonly Found<Malformed>[],
  thrownDefaults: readonly ThrownDefault[],
): Found<Malformed>[] {
  return definitions.flatMap(({ service, name, place, definition }): Found<Malformed>[] => {
    const ref = { service, name };
    if (opaque.some((f) => sameRef(f.violation.definition, ref))) return [];
    const converted = thrownDefaults.find((t) => t.definition === definition);
    const conversion: Found<Malformed>[] =
      converted === undefined
        ? []
        : [
            {
              violation: { kind: "Malformed.defaultSchema", definition: ref, data: {} },
              place,
              error: thrown(converted.error),
            },
          ];
    if (definition.kind === "entity") {
      if (converted !== undefined || !definition.single) return conversion;
      const error = defaultsError(definition.fields);
      if (error === undefined) return [];
      return [{ violation: { kind: "Malformed.defaultSchema", definition: ref, data: {} }, place, error }];
    }
    const chart = chartOf(definition);
    if (chart === undefined) return conversion;
    return [
      ...conversion,
      ...mapStates(chart.states).flatMap(([map, node]): Found<Malformed>[] => {
        const error = defaultsError(node.context ?? {});
        if (error === undefined) return [];
        return [{ violation: { kind: "Malformed.defaultSchema", definition: ref, data: { map } }, place, error }];
      }),
    ];
  });
}
