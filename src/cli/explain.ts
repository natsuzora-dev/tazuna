import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { haltingFaultKinds } from "../data/fault.generated.ts";
import { groups } from "../data/groups.ts";
import { haltingInvalidInputKinds } from "../data/invalidInput.generated.ts";
import { haltingInvalidScenarioKinds } from "../data/invalidScenario.generated.ts";
import { type Group, isUserKind, parseKind, type UserKind } from "../data/kinds.ts";
import type { Json } from "../data/values.ts";

/** The lines `from` to `to` of a file of an example's spec: the top-level statement that holds `line`, the reported one. */
export interface Excerpt {
  readonly file: string;
  readonly from: number;
  readonly to: number;
  readonly line: number;
  readonly text: string;
}

/** A violation that the fixture named after its kind reports, and the excerpt at its location if it names a line. */
export interface Example {
  readonly excerpt?: Excerpt;
  readonly violation: Json;
}

/**
 * The data that `explain` reads: the first sentence of each group's doc comment, and each kind's doc comment and
 * example. scripts/explain.ts builds it from src/data and the fixtures, which the package does not ship.
 */
export interface Explanations {
  readonly groups: Readonly<Record<Group, string>>;
  readonly kinds: Readonly<Record<UserKind, { readonly meaning: string; readonly example?: Example }>>;
}

/** What `explain` prints of a kind, as one JSON line. `halts` is present for the groups whose kinds can halt the run. */
export interface Explanation {
  readonly kind: UserKind;
  readonly meaning: string;
  readonly group: Group;
  readonly groupMeaning: string;
  readonly reportedBy: readonly string[];
  readonly fixedIn: string;
  readonly halts?: boolean;
  readonly example?: Example;
}

export const explanationsPath = join(import.meta.dirname, "../../explain.json");

/** The kinds that halt the run, for each group whose violations can. */
const halting: Partial<Record<Group, ReadonlySet<string>>> = {
  Fault: new Set(haltingFaultKinds),
  InvalidInput: new Set(haltingInvalidInputKinds),
  InvalidScenario: new Set(haltingInvalidScenarioKinds),
};

/**
 * The explanation of the kind that `text` names, from the explanations at `path`, or a misuse when `text` names no kind
 * or an internal kind (internalKinds), or `path` is missing.
 */
export function explain(
  text: string,
  path = explanationsPath,
): { readonly explanation: Explanation } | { readonly misuse: string } {
  const parsed = parseKind(text);
  if (parsed === undefined) return { misuse: `unknown kind ${text}` };
  const { kind, group } = parsed;
  if (!isUserKind(kind))
    return {
      misuse: `${kind} is internal to tazuna, and a spec that check passes never reports it. Report it as a bug`,
    };
  if (!existsSync(path)) return { misuse: `${path} is missing. Reinstall tazuna` };
  const explanations = JSON.parse(readFileSync(path, "utf8")) as Explanations;
  const { meaning, example } = explanations.kinds[kind];
  const { reportedBy, fixedIn } = groups[group];
  const halts = halting[group]?.has(kind);
  return {
    explanation: {
      kind,
      meaning,
      group,
      groupMeaning: explanations.groups[group],
      reportedBy,
      fixedIn,
      ...(halts === undefined ? {} : { halts }),
      ...(example === undefined ? {} : { example }),
    },
  };
}
