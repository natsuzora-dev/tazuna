import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Track = entity({ description: "A track", fields: { id: z.string() }, key: "id" });

export const { command, machine, event, contract } = service({
  name: "player",
  description: "Play tracks",
  entities: { Track },
});

export const paused = event({});

export const pause = command({ callers: ["client"], emits: [paused] }).decide(() => [emit(paused, {})]);

// A history state under a map state enters the map state's initial state, so it restores nothing.
export const shuffler = machine({
  description: "Play each track, returning to where it was after a pause",
  receives: { paused },
  initial: "tracks",
  states: {
    tracks: {
      type: "map",
      key: { trackId: z.string() },
      initial: "playing",
      states: { playing: { held: { trackId: z.string() } }, back: { type: "history" } },
    },
  },
}).chart({
  states: {
    tracks: {
      items: ({ records }) => records.Track.map((t) => ({ trackId: t.id })),
      initial: { with: { trackId: ({ key }) => key.trackId } },
    },
  },
});

// Returning through the history state of on would enter playing without an edge that fills its track.
export const player = machine({
  description: "Play a track, and return to what was playing after a pause",
  receives: { paused },
  initial: "on",
  states: {
    on: {
      initial: "idle",
      states: { idle: {}, playing: { held: { trackId: z.string() } }, back: { type: "history" } },
    },
    pausedNow: {},
  },
}).chart({
  states: {
    idle: { on: { paused: [{ target: "playing", with: { trackId: () => "track-1" } }] } },
    playing: { on: { paused: [{ target: "pausedNow" }] } },
    pausedNow: { on: { paused: [{ target: "back" }] } },
  },
});

export const playerContract = contract({ pause });
