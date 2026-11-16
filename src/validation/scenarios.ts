import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import type { Illegal } from "../data/illegal.generated.ts";
import type { Structure } from "../syntax/structure.generated.ts";

type ScenarioInput = Structure["scenarios"][number]["inputs"][number];

import { type DefinitionStructure, isKeyOf } from "../syntax/structure.ts";

function requests(d: DefinitionStructure, target: DefinitionRef): boolean {
  if (d.kind === "automation") return sameRef(d.command, target);
  if (d.kind === "machine" || d.kind === "screen")
    return (
      Object.values(d.commands).some((c) => sameRef(c, target)) ||
      Object.values(d.queries).some((q) => sameRef(q, target))
    );
  return false;
}

function unrequestedAnswers(structure: Structure): Illegal[] {
  return structure.scenarios.flatMap((sc) =>
    sc.inputs.flatMap((input, i): Illegal[] => {
      if (input.type !== "answer" || input.sender === null || input.target === null) return [];
      const { sender, target } = input;
      return structure.definitions.some((d) => sameRef(d, sender) && requests(d, target))
        ? []
        : [
            {
              kind: "Illegal.unrequestedAnswer",
              definition: null,
              scenario: { service: sc.service, name: sc.name },
              input: i + 1,
              data: {},
            },
          ];
    }),
  );
}

/** Lean's ScenarioInput.named: the positions of the input that the input names. */
function named(input: ScenarioInput): readonly number[] | null {
  if (input.type === "event") return input.resultOf;
  return input.type === "unsubscribe" ? input.subscription : null;
}

function namedInputsPlacedTwice(structure: Structure): Illegal[] {
  return structure.scenarios.flatMap((sc) =>
    sc.inputs.flatMap((input, i): Illegal[] => {
      const positions = named(input);
      return positions !== null && 1 < positions.length
        ? [
            {
              kind: "Illegal.namedInputPlacedTwice",
              definition: null,
              scenario: { service: sc.service, name: sc.name },
              input: i + 1,
              data: {},
            },
          ]
        : [];
    }),
  );
}

function namedInputsUnplaced(structure: Structure): Illegal[] {
  return structure.scenarios.flatMap((sc) =>
    sc.inputs.flatMap((input, i): Illegal[] => {
      const positions = named(input);
      return positions !== null && !positions.some((p) => p < i)
        ? [
            {
              kind: "Illegal.namedInputUnplaced",
              definition: null,
              scenario: { service: sc.service, name: sc.name },
              input: i + 1,
              data: {},
            },
          ]
        : [];
    }),
  );
}

function scenariosOfExternalServices(structure: Structure): Illegal[] {
  return structure.scenarios.flatMap((sc): Illegal[] =>
    structure.services.some((sv) => sv.name === sc.service && sv.external)
      ? [
          {
            kind: "Illegal.scenarioOfExternalService",
            definition: null,
            scenario: { service: sc.service, name: sc.name },
            data: {},
          },
        ]
      : [],
  );
}

function countedKeys(structure: Structure): Illegal[] {
  const keyed = structure.definitions.filter((d) => d.kind === "entity" && d.key !== null);
  return structure.scenarios.flatMap((sc) =>
    sc.inputs.flatMap((input, i): Illegal[] =>
      [...new Set("strings" in input ? input.strings : [])].flatMap((value): Illegal[] => {
        const entity = keyed.find((e) => isKeyOf(e.name, value));
        return entity === undefined
          ? []
          : [
              {
                kind: "Illegal.countedKey",
                definition: null,
                scenario: { service: sc.service, name: sc.name },
                input: i + 1,
                data: { value, entity: { service: entity.service, name: entity.name } },
              },
            ];
      }),
    ),
  );
}

export function check(structure: Structure): Illegal[] {
  return [
    ...unrequestedAnswers(structure),
    ...namedInputsPlacedTwice(structure),
    ...namedInputsUnplaced(structure),
    ...scenariosOfExternalServices(structure),
    ...countedKeys(structure),
  ];
}
