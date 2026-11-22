import { relative, sep } from "node:path";
import type { NotConverted } from "../../convert/program.ts";
import type { Restricted } from "../../data/restricted.ts";
import { type Found, placeOf } from "../../load/found.ts";
import type { Spec } from "../../load/load.ts";

/** A function whose binds stay outside the IR stays outside too, so only the binds are reported. */
const followsBinds = (n: NotConverted) => n.reason === "reads binds that stay TS";

/**
 * Restricted.function for each spec function that the converter leaves outside the IR, once per function source,
 * at the start of the function, or at its definition when the converter found no source.
 */
export function check(spec: Spec, notConverted: readonly NotConverted[]): Found<Restricted>[] {
  const seen = new Set<string>();
  return notConverted.flatMap((n): Found<Restricted>[] => {
    if (followsBinds(n)) return [];
    const at = n.location;
    const place =
      at === undefined
        ? placeOf(spec, n.definition)
        : { file: relative(spec.root, at.file).split(sep).join("/"), line: at.line + 1, column: at.column + 1 };
    const key = JSON.stringify(place);
    if (seen.has(key)) return [];
    seen.add(key);
    return [
      { violation: { kind: "Restricted.function", definition: n.definition, data: { reason: n.reason } }, place },
    ];
  });
}
