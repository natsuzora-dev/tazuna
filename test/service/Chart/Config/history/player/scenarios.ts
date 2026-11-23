import { parseInstant } from "@natsuzora-dev/tazuna";
import { given, pause, play, scenario, skip, skipTrack, startTrack, tuneRadio } from "./player.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [] });

export const resumeWhereStopped = scenario({
  description:
    "Play, skip, pause, and play; song has not exited playing yet, so the first play enters intro, the initial state of playing, through the history state resumed. The play after the pause in chorus reenters chorus, where song was when it exited playing",
  given: arranged,
  when: (w) => {
    w.client.as("client").send(play, {});
    w.client.as("client").send(skip, {});
    w.client.as("client").send(pause, {});
    w.client.as("client").send(play, {});
  },
  then: () => [],
});

export const historyInCopy = scenario({
  description:
    "Start a track, skip it, and start it again; the copy t1 of playlist has not exited tracks, so entering the history state again on skipTrack enters waiting, the initial state of tracks, instead of the last state playing, and plays no track. The next startTrack enters playing and plays again",
  given: arranged,
  when: (w) => {
    w.client.as("client").send(startTrack, {});
    w.client.as("client").send(skipTrack, {});
    w.client.as("client").send(startTrack, {});
  },
  then: () => [],
});

export const historyAtRoot = scenario({
  description:
    "Tune the radio three times; the history state back of radio sits directly under the chart and has no parent state to record, so entering back on the second tuneRadio enters silent, the initial state of the chart, and plays nothing. The third tuneRadio enters tuned and plays again",
  given: arranged,
  when: (w) => {
    w.client.as("client").send(tuneRadio, {});
    w.client.as("client").send(tuneRadio, {});
    w.client.as("client").send(tuneRadio, {});
  },
  then: () => [],
});
