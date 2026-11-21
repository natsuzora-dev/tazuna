import { domain, explore } from "@natsuzora-dev/tazuna";
import { greet, join } from "./welcome.ts";

export const welcomeExplore = explore({
  service: "welcome",
  depth: 2,
  domains: [domain(join.input.nickname, [""]), domain(greet.input.name, ["rejected"])],
});
