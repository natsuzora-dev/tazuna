import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { pause, play, skip, skipTrack, startTrack, tuneRadio } from "./player.ts";

export const resumeWhereStopped = scenario(
  "Play, skip, pause, and play; song has not exited playing yet, so the first play enters intro, the initial state of playing, through the history state resumed. The play after the pause in chorus reenters chorus, where song was when it exited playing",
  [at("2026-10-25T10:00:00+09:00"), send(play, {}), send(skip, {}), send(pause, {}), send(play, {})],
);

export const historyInCopy = scenario(
  "Start a track, skip it, and start it again; the copy t1 of playlist has not exited tracks, so entering the history state again on skipTrack enters waiting, the initial state of tracks, instead of the last state playing, and plays no track. The next startTrack enters playing and plays again",
  [at("2026-10-25T10:00:00+09:00"), send(startTrack, {}), send(skipTrack, {}), send(startTrack, {})],
);

export const historyAtRoot = scenario(
  "Tune the radio three times; the history state back of radio sits directly under the chart and has no parent state to record, so entering back on the second tuneRadio enters silent, the initial state of the chart, and plays nothing. The third tuneRadio enters tuned and plays again",
  [at("2026-10-25T10:00:00+09:00"), send(tuneRadio, {}), send(tuneRadio, {}), send(tuneRadio, {})],
);
