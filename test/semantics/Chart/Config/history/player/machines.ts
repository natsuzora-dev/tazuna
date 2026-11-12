import { z } from "zod";
import {
  machine,
  pausePressed,
  playChorus,
  playIntro,
  playPressed,
  playTrack,
  radioTuned,
  skipPressed,
  trackSkipped,
  trackStarted,
} from "./player.ts";

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

export const playlist = machine({
  description: "Play each track in its copy, and go to again when skip is pressed for the track",
  receives: { trackStarted, trackSkipped },
  commands: { playTrack },
  initial: "tracks",
  states: {
    tracks: {
      type: "map",
      key: { track: z.string() },
      initial: "waiting",
      states: { waiting: {}, playing: {}, again: { type: "history" } },
    },
  },
}).chart({
  states: {
    tracks: { items: () => [{ track: "t1" }] },
    waiting: { on: { trackStarted: [{ target: "playing" }] } },
    playing: {
      on: { trackSkipped: [{ target: "again" }] },
      sends: { playTrack: { input: ({ key }) => key, onAccepted: [] } },
    },
  },
});

export const radio = machine({
  description: "Alternate between playing and stopping each time the radio is tuned",
  receives: { radioTuned },
  commands: { playTrack },
  initial: "silent",
  states: { silent: {}, tuned: {}, back: { type: "history" } },
}).chart({
  states: {
    silent: { on: { radioTuned: [{ target: "tuned" }] } },
    tuned: {
      on: { radioTuned: [{ target: "back" }] },
      sends: { playTrack: { input: () => ({ track: "radio" }), onAccepted: [] } },
    },
  },
});
