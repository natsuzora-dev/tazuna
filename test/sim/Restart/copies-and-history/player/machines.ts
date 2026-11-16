import { ref } from "@natsuzora-dev/tazuna";
import { loadTrack, machine, pausePressed, playChorus, playIntro, playPressed, skipPressed, Track } from "./player.ts";

export const song = machine({
  description: "Resume the song where it was paused",
  receives: { playPressed, skipPressed, pausePressed },
  commands: { playIntro, playChorus },
  initial: "paused",
  states: {
    paused: {},
    playing: { initial: "intro", states: { intro: {}, chorus: {}, resumed: { type: "history" } } },
  },
}).chart({
  states: {
    paused: { on: { playPressed: [{ target: "resumed" }] } },
    playing: { on: { pausePressed: [{ target: "paused" }] } },
    intro: {
      on: { skipPressed: [{ target: "chorus" }] },
      sends: { playIntro: { onAccepted: [] } },
    },
    chorus: { sends: { playChorus: { onAccepted: [] } } },
  },
});

export const loader = machine({
  description: "Load each queued track in its copy",
  commands: { loadTrack },
  initial: "tracks",
  states: {
    tracks: { type: "map", key: { trackId: ref(Track) }, initial: "loading", states: { loading: {}, loaded: {} } },
  },
}).chart({
  states: {
    tracks: { items: ({ records }) => records.Track.map((t) => ({ trackId: t.id })) },
    loading: { sends: { loadTrack: { input: ({ key }) => key, onAccepted: [{ target: "loaded" }] } } },
  },
});
