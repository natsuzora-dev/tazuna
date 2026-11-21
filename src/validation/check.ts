import type { Illegal } from "../data/illegal.generated.ts";
import type { Structure } from "../spec/structure.generated.ts";
import * as automations from "./automations.ts";
import * as charts from "./charts.ts";
import * as commands from "./commands.ts";
import * as contracts from "./contracts.ts";
import * as explores from "./explores.ts";
import * as schemas from "./schemas.ts";

export function check(structure: Structure): Illegal[] {
  return [
    ...automations.check(structure),
    ...charts.check(structure),
    ...commands.check(structure),
    ...contracts.check(structure),
    ...schemas.check(structure),
    ...explores.check(structure),
  ];
}
