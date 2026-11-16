import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { join } from "./welcome.ts";

export const joinNameless = scenario(
  "Join with an empty nickname; greetJoined sends greet with the empty nickname, which fails the input schema of greet, so test reports automationInputSchema",
  [at("2026-10-25T09:00:00+09:00"), send(join, { nickname: "" })],
);
