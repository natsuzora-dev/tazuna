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

type Scenario = Structure["scenarios"][number];
type ScenarioLine = Scenario["inputs"][number];

const scenarioIllegal = <K extends string, D>(sc: Scenario, kind: K, input: number, data: D) => ({
  kind,
  definition: null,
  scenario: { service: sc.service, name: sc.name },
  input,
  data,
});

function unrequestedAnswers(structure: Structure): Illegal[] {
  return structure.scenarios.flatMap((sc) =>
    sc.inputs.flatMap((l, i): Illegal[] => {
      if (l.type !== "answer" || l.sender === null || l.target === null) return [];
      const { sender, target } = l;
      return structure.definitions.some((d) => sameRef(d, sender) && requests(d, target))
        ? []
        : [scenarioIllegal(sc, "Illegal.unrequestedAnswer", i + 1, {})];
    }),
  );
}

/** Lean's ScenarioLine.keyNames: the names that the line's `keys` gives, each with its entity name. */
const keyNames = (l: ScenarioLine): (readonly [string, string])[] =>
  Object.entries(l.keys).flatMap(([e, names]) => names.map((n) => [e, n] as const));

/** Lean's runsOf: the run of the scenario's service, then the runs of the peers of its elsewhere lines. */
const runsOf = (sc: Scenario): (string | null)[] => [...new Set([null, ...sc.inputs.map((l) => l.run)])];

/** Lean's runLines: the lines of the run `run`, the state that the scenario gives its peer first, with no index. */
function runLines(structure: Structure, sc: Scenario, run: string | null): [ScenarioLine, number | null][] {
  const given = run === null ? undefined : sc.given.find((g) => g.service === run);
  const state = given === undefined ? [] : (structure.scenarios.find((t) => sameRef(t, given))?.inputs ?? []);
  return [
    ...state.map((l): [ScenarioLine, null] => [l, null]),
    ...sc.inputs.flatMap((l, i): [ScenarioLine, number][] => (l.run === run ? [[l, i]] : [])),
  ];
}

/** Lean's scopedLines: each line of the scenario, by run, with its index, the lines of its run before it, and all. */
function scopedLines(structure: Structure, sc: Scenario) {
  return runsOf(sc).flatMap((r) => {
    const lines = runLines(structure, sc, r);
    return lines.flatMap(([l, i], k) =>
      i === null ? [] : [{ i, l, before: lines.slice(0, k).map(([b]) => b), all: lines.map(([a]) => a) }],
    );
  });
}

function namedInputsPlacedTwice(structure: Structure): Illegal[] {
  return structure.scenarios.flatMap((sc) =>
    scopedLines(structure, sc).flatMap(({ i, l, all }): Illegal[] =>
      l.names !== null && all.filter((a) => a.handle === l.names).length > 1
        ? [scenarioIllegal(sc, "Illegal.namedInputPlacedTwice", i + 1, {})]
        : [],
    ),
  );
}

function namedInputsUnplaced(structure: Structure): Illegal[] {
  return structure.scenarios.flatMap((sc) =>
    scopedLines(structure, sc).flatMap(({ i, l, before }): Illegal[] =>
      l.names !== null && !before.some((b) => b.handle === l.names && b.sentBy === l.sentBy)
        ? [scenarioIllegal(sc, "Illegal.namedInputUnplaced", i + 1, {})]
        : [],
    ),
  );
}

const samePair = (a: readonly [string, string]) => (b: readonly [string, string]) => a[0] === b[0] && a[1] === b[1];

function keysNamedTwice(structure: Structure): Illegal[] {
  return structure.scenarios.flatMap((sc) =>
    scopedLines(structure, sc).flatMap(({ i, l, before }): Illegal[] => {
      const pairs = keyNames(l);
      const twice = pairs.find(
        (p, j) => before.some((b) => keyNames(b).some(samePair(p))) || pairs.slice(0, j).some(samePair(p)),
      );
      return twice === undefined
        ? []
        : [scenarioIllegal(sc, "Illegal.keyNamedTwice", i + 1, { entity: twice[0], name: twice[1] })];
    }),
  );
}

function keysUsedBeforeNamed(structure: Structure): Illegal[] {
  return structure.scenarios.flatMap((sc) =>
    sc.inputs.flatMap((l, i): Illegal[] => {
      const name = l.strings.find((v) => sc.inputs.slice(i + 1).some((m) => keyNames(m).some(([, n]) => n === v)));
      return name === undefined ? [] : [scenarioIllegal(sc, "Illegal.keyUsedBeforeNamed", i + 1, { name })];
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
  return structure.scenarios.flatMap((sc) => {
    const entities = keyed.filter((e) => e.service === sc.service || sc.peers.includes(e.service));
    return sc.inputs.flatMap((l, i): Illegal[] =>
      [...new Set([...l.strings, ...keyNames(l).map(([, n]) => n)])].flatMap((value): Illegal[] => {
        const entity = entities.find((e) => isKeyOf(e.name, value));
        return entity === undefined
          ? []
          : [
              scenarioIllegal(sc, "Illegal.countedKey", i + 1, {
                value,
                entity: { service: entity.service, name: entity.name },
              }),
            ];
      }),
    );
  });
}

export function check(structure: Structure): Illegal[] {
  return [
    ...unrequestedAnswers(structure),
    ...namedInputsPlacedTwice(structure),
    ...namedInputsUnplaced(structure),
    ...scenariosOfExternalServices(structure),
    ...countedKeys(structure),
    ...keysNamedTwice(structure),
    ...keysUsedBeforeNamed(structure),
  ];
}
