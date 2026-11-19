import { pause, play, queueTrack, scenario, skip } from "./player.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: { Track: [] }, peers: [] } as const;

export const historyReset = scenario(
  "Play, skip, pause, restart, and play; the restart forgets that song was last in chorus, so the play after it enters intro, the initial state of playing, through the history state resumed",
  {
    given,
    when: (w) => {
      w.client.send(play, {});
      w.client.send(skip, {});
      w.client.send(pause, {});
      w.host.restart();
      w.client.send(play, {});
    },
    then: () => [],
  },
);

export const copiesRebuilt = scenario(
  "Queue t1 and restart; loader runs a copy for t1 from the records again when it begins, so it loads t1 again",
  {
    given,
    when: (w) => {
      w.client.send(queueTrack, { trackId: "t1" });
      w.host.restart();
    },
    then: () => [],
  },
);
