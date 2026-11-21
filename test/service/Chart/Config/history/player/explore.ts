import { domain, explore } from "@natsuzora-dev/tazuna";
import { playTrack } from "./player.ts";

export const playerExplore = explore({ service: "player", depth: 2, domains: [domain(playTrack.input.track, ["a"])] });
