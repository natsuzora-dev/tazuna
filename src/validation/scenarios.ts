import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import type { Illegal } from "../data/illegal.generated.ts";
import type { Structure } from "../syntax/structure.generated.ts";
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

function resultsOfPlacedTwice(structure: Structure): Illegal[] {
  return structure.scenarios.flatMap((sc) =>
    sc.inputs.flatMap((input, i): Illegal[] =>
      input.type === "event" && input.resultOf !== null && 1 < input.resultOf.length
        ? [
            {
              kind: "Illegal.resultOfPlacedTwice",
              definition: null,
              scenario: { service: sc.service, name: sc.name },
              input: i + 1,
              data: {},
            },
          ]
        : [],
    ),
  );
}

function resultsOfUnplaced(structure: Structure): Illegal[] {
  return structure.scenarios.flatMap((sc) =>
    sc.inputs.flatMap((input, i): Illegal[] =>
      input.type === "event" && input.resultOf !== null && !input.resultOf.some((p) => p < i)
        ? [
            {
              kind: "Illegal.resultOfUnplaced",
              definition: null,
              scenario: { service: sc.service, name: sc.name },
              input: i + 1,
              data: {},
            },
          ]
        : [],
    ),
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
    ...resultsOfPlacedTwice(structure),
    ...resultsOfUnplaced(structure),
    ...scenariosOfExternalServices(structure),
    ...countedKeys(structure),
  ];
}
