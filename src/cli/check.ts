import { sameRef } from "../data/definitionRef.ts";
import type { Illegal } from "../data/illegal.generated.ts";
import type { Malformed } from "../data/malformed.ts";
import type { NonCanonical } from "../data/nonCanonical.ts";
import type { Problem } from "../data/problem.ts";
import type { Restricted } from "../data/restricted.ts";
import type { Place } from "../dsl/definition.ts";
import { comparePlaces, type Found, placeOf, problemOfFound } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import * as binds from "../load/nonCanonical/binds.ts";
import * as charts from "../load/nonCanonical/charts.ts";
import * as constants from "../load/nonCanonical/constants.ts";
import * as descriptions from "../load/nonCanonical/descriptions.ts";
import * as rejections from "../load/nonCanonical/rejections.ts";
import * as sources from "../load/restricted/sources.ts";
import { check as validate } from "../validation/check.ts";

const syntaxChecks: readonly { readonly check: (spec: Spec) => readonly Found<NonCanonical | Restricted>[] }[] = [
  binds,
  charts,
  constants,
  descriptions,
  rejections,
  sources,
];

function placeOfIllegal(spec: Spec, illegal: Illegal): Place {
  switch (illegal.kind) {
    case "Illegal.unrequestedAnswer":
    case "Illegal.resultOfPlacedTwice":
    case "Illegal.resultOfUnplaced":
    case "Illegal.scenarioOfExternalService": {
      const { service, name } = illegal.scenario;
      const scenario = spec.scenarios.find((s) => sameRef(s, illegal.scenario));
      if (scenario === undefined) throw new Error(`no scenario ${service}.${name}`);
      return scenario.place;
    }
    case "Illegal.foreignMember": {
      const contract = spec.contracts.find((c) => c.service === illegal.data.contract);
      if (contract === undefined) throw new Error(`no contract of ${illegal.data.contract}`);
      return contract.place;
    }
    case "Illegal.automationCycle":
    case "Illegal.missingParent":
    case "Illegal.ownQuery":
    case "Illegal.alwaysCycle":
    case "Illegal.foreignEvent":
      return placeOf(spec, illegal.definition);
  }
}

export function check(spec: Spec): Problem[] {
  const loading = [...spec.malformed, ...syntaxChecks.flatMap((c) => c.check(spec))];
  const found: Found<Malformed | NonCanonical | Restricted | Illegal>[] =
    spec.malformed.length > 0
      ? loading
      : [
          ...loading,
          ...validate(spec.structure).map((violation) => ({ violation, place: placeOfIllegal(spec, violation) })),
        ];
  return found.sort(({ place: x }, { place: y }) => comparePlaces(x, y)).map(problemOfFound);
}
