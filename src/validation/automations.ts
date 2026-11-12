import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import type { Illegal } from "../data/illegal.generated.ts";
import type { Structure } from "../syntax/structure.generated.ts";
import { emitsOf } from "../syntax/structure.ts";

interface Automation {
  /** The position among the automations that send a command to their own service, in definition order. */
  readonly index: number;
  readonly ref: DefinitionRef;
  readonly receives: DefinitionRef | null;
  readonly command: DefinitionRef | null;
}

function automations(structure: Structure): Automation[] {
  return structure.definitions
    .flatMap((d) =>
      d.kind === "automation" && d.command?.service === d.service
        ? [{ ref: { service: d.service, name: d.name }, receives: d.receives, command: d.command }]
        : [],
    )
    .map((a, index) => ({ index, ...a }));
}

/**
 * Returns the chains from `last` back to the automation at `start`, each automation receiving an event that the command
 * of the one before emits. `chain` holds the automations after the start so far. Only automations defined after the
 * start and not yet in the chain (`rest`) are followed, so that each cycle is found once, from its first automation.
 */
function walk(
  structure: Structure,
  as: readonly Automation[],
  start: number,
  rest: readonly number[],
  last: Automation,
  chain: readonly DefinitionRef[],
): (readonly DefinitionRef[])[] {
  return emitsOf(structure, last.command).flatMap((emitted) =>
    as
      .filter((n) => sameRef(n.receives, emitted))
      .flatMap((n) =>
        n.index === start
          ? [chain]
          : start < n.index && rest.includes(n.index)
            ? walk(
                structure,
                as,
                start,
                rest.filter((i) => i !== n.index),
                n,
                [...chain, n.ref],
              )
            : [],
      ),
  );
}

export function check(structure: Structure): Illegal[] {
  const as = automations(structure);
  return as.flatMap((a) =>
    walk(
      structure,
      as,
      a.index,
      as.map((n) => n.index).filter((i) => i !== a.index),
      a,
      [],
    ).map((chain): Illegal => ({ kind: "Illegal.automationCycle", definition: a.ref, data: { chain } })),
  );
}
