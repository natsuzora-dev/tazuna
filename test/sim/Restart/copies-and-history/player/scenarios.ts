import { at, restart, scenario, send } from "@natsuzora-dev/tazuna";
import { pause, play, queueTrack, skip } from "./player.ts";

export const historyReset = scenario(
  "Play, skip, pause, restart, and play; the restart forgets that song was last in chorus, so the play after it enters intro, the initial state of playing, through the history state resumed",
  [at("2026-10-25T10:00:00+09:00"), send(play, {}), send(skip, {}), send(pause, {}), restart(), send(play, {})],
);

export const copiesRebuilt = scenario(
  "Queue t1 and restart; loader runs a copy for t1 from the records again when it begins, so it loads t1 again",
  [at("2026-10-25T10:00:00+09:00"), send(queueTrack, { trackId: "t1" }), restart()],
);
