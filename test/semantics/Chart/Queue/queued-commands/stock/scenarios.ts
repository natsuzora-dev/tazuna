import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { start } from "./stock.ts";

export const copyInAlwaysStep = scenario(
  "Start; when prepare emits prepared and creates an Item record, a processing step starts that evaluates only the always transitions of packer, and in that evaluation packer enters items, the copy x starts, and x adds x to names. The processing step of the answer to prepare reads names, and the two processing steps have no order. The answer step also evaluates the always transitions before its work, which starts the copy x, so in either order packer enters counting and sends count, and tazuna reports no pair of the step that starts the copy x and the answer step",
  [at("2026-10-25T10:00:00+09:00"), send(start, {})],
);
