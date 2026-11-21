import { domain, explore } from "@natsuzora-dev/tazuna";
import { loadTrack, Track } from "./player.ts";

export const playerExplore = explore({
  service: "player",
  depth: 2,
  domains: [domain(Track.fields.id, ["t1"]), domain(loadTrack.input.trackId, ["t1"])],
});
