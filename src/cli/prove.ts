import type { CheckedSpec } from "../check/spec.ts";
import { InternalError } from "../data/internalError.ts";
import type { Location } from "../data/violation.ts";
import { placeOf } from "../load/found.ts";
import { solve } from "../z3/solve.ts";
import { ask } from "./engine.ts";
import type { ProveResult } from "./protocol.generated.ts";

/** A result of prove at the definition that declares its invariant: the entity, the machine or screen, or the service. */
export type ProveLine = ProveResult & { readonly location: Location };

function locationOf(spec: CheckedSpec, { invariant: { definition } }: ProveResult): Location {
  const service = definition.name === definition.service ? spec.services.get(definition.service) : undefined;
  const { file, line } = service?.place ?? placeOf(spec, definition);
  return { file, line };
}

/** prove's result of each invariant of each spec service: the engine writes the queries and reads Z3's answers. */
export async function proveSpec(spec: CheckedSpec): Promise<ProveLine[]> {
  const [queried] = ask("proveQueries", [{ structure: spec.structure }]);
  if (queried === undefined) throw new InternalError("the engine gave no queries to prove");
  const answers = await solve(queried.scripts);
  const [proved] = ask("prove", [{ structure: spec.structure, answers }]);
  if (proved === undefined) throw new InternalError("the engine gave no results of prove");
  return proved.results.map((r) => ({ ...r, location: locationOf(spec, r) }));
}
