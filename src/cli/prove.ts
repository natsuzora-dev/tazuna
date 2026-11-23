import type { CheckedSpec } from "../check/spec.ts";
import type { Location } from "../data/violation.ts";
import { placeOf } from "../load/found.ts";
import { solve } from "../z3/solve.ts";
import { converse } from "./engine.ts";
import type { ProveResult } from "./protocol.generated.ts";

/** A result of prove at the definition that declares its property: an entity, a command or query, a chart, or the service. */
export type ProveLine = ProveResult & { readonly location: Location };

function locationOf(spec: CheckedSpec, { property: { definition } }: ProveResult): Location {
  const service = definition.name === definition.service ? spec.services.get(definition.service) : undefined;
  const { file, line } = service?.place ?? placeOf(spec, definition);
  return { file, line };
}

/** prove's result of each property of each spec service: the engine writes the queries and reads Z3's answers. */
export async function proveSpec(spec: CheckedSpec): Promise<ProveLine[]> {
  const { results } = await converse("prove", { structure: spec.structure }, solve);
  return results.map((r) => ({ ...r, location: locationOf(spec, r) }));
}
