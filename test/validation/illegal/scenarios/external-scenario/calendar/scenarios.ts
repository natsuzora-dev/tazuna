import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addReminder } from "./calendar.ts";

export const addOne = scenario("Add a reminder to the external calendar; check reports scenarioOfExternalService", [
  at("2026-10-26T00:00:00Z"),
  send(addReminder, {}),
]);
