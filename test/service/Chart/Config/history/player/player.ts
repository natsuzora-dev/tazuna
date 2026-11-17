import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, contract, scenario } = service({ name: "player", description: "Play songs" });

export const playPressed = event({});
export const skipPressed = event({});
export const pausePressed = event({});
export const introPlayed = event({});
export const chorusPlayed = event({});
export const trackStarted = event({});
export const trackSkipped = event({});
export const radioTuned = event({});
export const trackPlayed = event({ payload: { track: z.string() } });

export const play = command({ emits: [playPressed] }).decide(() => [emit(playPressed, {})]);
export const skip = command({ emits: [skipPressed] }).decide(() => [emit(skipPressed, {})]);
export const pause = command({ emits: [pausePressed] }).decide(() => [emit(pausePressed, {})]);
export const playIntro = command({ emits: [introPlayed] }).decide(() => [emit(introPlayed, {})]);
export const playChorus = command({ emits: [chorusPlayed] }).decide(() => [emit(chorusPlayed, {})]);
export const startTrack = command({ emits: [trackStarted] }).decide(() => [emit(trackStarted, {})]);
export const skipTrack = command({ emits: [trackSkipped] }).decide(() => [emit(trackSkipped, {})]);
export const tuneRadio = command({ emits: [radioTuned] }).decide(() => [emit(radioTuned, {})]);
export const playTrack = command({
  input: { track: z.string() },
  emits: [trackPlayed],
}).decide(({ input }) => [emit(trackPlayed, { track: input.track })]);
