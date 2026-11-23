import { parseInstant } from "@natsuzora-dev/tazuna";
import { given, pause, play, queueTrack, scenario, skip } from "./player.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: { Track: [] }, peers: [] });

export const historyReset = scenario({
  description:
    "Play, skip, pause, restart, and play; the restart forgets that song was last in chorus, so the play after it enters intro, the initial state of playing, through the history state resumed",
  given: arranged,
  when: (w) => {
    w.client.as("client").send(play, {});
    w.client.as("client").send(skip, {});
    w.client.as("client").send(pause, {});
    w.host.restart();
    w.client.as("client").send(play, {});
  },
  then: () => [],
});

export const copiesRebuilt = scenario({
  description:
    "Queue t1 and restart; loader runs a copy for t1 from the records again when it begins, so it loads t1 again",
  given: arranged,
  when: (w) => {
    w.client.as("client").send(queueTrack, { trackId: "t1" });
    w.host.restart();
  },
  then: () => [],
});
