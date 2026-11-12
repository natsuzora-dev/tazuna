import type { Illegal } from "../data/illegal.generated.ts";
import type { Structure } from "../syntax/structure.generated.ts";
import * as automations from "./automations.ts";
import * as charts from "./charts.ts";
import * as commands from "./commands.ts";
import * as contracts from "./contracts.ts";
import * as scenarios from "./scenarios.ts";

export function check(structure: Structure): Illegal[] {
  return [
    ...automations.check(structure),
    ...charts.check(structure),
    ...commands.check(structure),
    ...contracts.check(structure),
    ...scenarios.check(structure),
  ];
}
