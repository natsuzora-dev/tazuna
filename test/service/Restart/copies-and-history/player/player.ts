import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Track = entity({ description: "A track in the queue", fields: { id: z.string() }, key: "id" });

export const { command, machine, event, createEvent, contract, given, scenario } = service({
  name: "player",
  description: "Play songs",
  entities: { Track },
});

export const trackQueued = createEvent({ entity: Track });
export const playPressed = event({});
export const skipPressed = event({});
export const pausePressed = event({});
export const introPlayed = event({});
export const chorusPlayed = event({});
export const trackLoaded = event({ payload: { trackId: z.string() } });

export const queueTrack = command({
  callers: ["client"],
  input: { trackId: Track.fields.id },
  emits: [trackQueued],
}).decide(({ input }) => [emit(trackQueued, { id: input.trackId })]);
export const play = command({ callers: ["client"], emits: [playPressed] }).decide(() => [emit(playPressed, {})]);
export const skip = command({ callers: ["client"], emits: [skipPressed] }).decide(() => [emit(skipPressed, {})]);
export const pause = command({ callers: ["client"], emits: [pausePressed] }).decide(() => [emit(pausePressed, {})]);
export const playIntro = command({ callers: ["client", "player"], emits: [introPlayed] }).decide(() => [
  emit(introPlayed, {}),
]);
export const playChorus = command({ callers: ["client", "player"], emits: [chorusPlayed] }).decide(() => [
  emit(chorusPlayed, {}),
]);
export const loadTrack = command({
  callers: ["client", "player"],
  input: { trackId: z.string() },
  emits: [trackLoaded],
}).decide(({ input }) => [emit(trackLoaded, { trackId: input.trackId })]);
