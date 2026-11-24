import type { NonCanonical } from "../../data/nonCanonical.ts";
import type { AnyCommand, Automation } from "../../dsl/definition.ts";
import { type Found, placeOf } from "../../load/found.ts";
import type { Spec } from "../../load/load.ts";
import type { Program } from "../../spec/ir.generated.ts";

const isBound = (value: unknown): boolean =>
  typeof value === "object" &&
  value !== null &&
  (value as { op?: unknown; arg?: unknown }).op === "arg" &&
  (value as { arg?: unknown }).arg === "bound";

/** Adds to `reads` each `bound.<name>` in the IR `value`, and returns whether it uses `bound` whole. */
function boundReads(value: unknown, reads: Set<string>): boolean {
  if (typeof value !== "object" || value === null) return false;
  if (Array.isArray(value)) return value.map((v) => boundReads(v, reads)).some(Boolean);
  const node = value as { readonly op?: unknown; readonly object?: unknown; readonly name?: unknown };
  if ((node.op === "field" || node.op === "fieldOpt") && isBound(node.object)) {
    reads.add(node.name as string);
    return false;
  }
  if (isBound(node)) return true;
  return Object.values(node)
    .map((v) => boundReads(v, reads))
    .some(Boolean);
}

/**
 * The binds of each command and automation that none of its converted functions reads: its decide or react, requires,
 * ensures and guard, where `bound` is an argument.
 */
export function check(spec: Spec, program: Program): Found<NonCanonical>[] {
  return spec.definitions.flatMap(({ service, name, definition: d }) => {
    if (d.kind !== "automation" && d.kind !== "command") return [];
    const names = Object.keys((d as Automation | AnyCommand).binds);
    if (names.length === 0) return [];
    const mine = (x: { readonly definition: { readonly service: string; readonly name: string } }) =>
      x.definition.service === service && x.definition.name === name;
    const bodies = [program.decide, program.react, program.requirement, program.ensures, program.automationGuard]
      .flat()
      .filter(mine);
    const reads = new Set<string>();
    if (boundReads(bodies, reads)) return [];
    const definition = { service, name };
    return names
      .filter((binding) => !reads.has(binding))
      .map((binding) => ({
        violation: { kind: "NonCanonical.unreadBinding", definition, data: { binding } },
        place: placeOf(spec, definition),
      }));
  });
}
