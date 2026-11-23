import { contract, pause, play, skip, skipTrack, startTrack, tuneRadio } from "./player.ts";

export const player = contract({ play, skip, pause, startTrack, skipTrack, tuneRadio });
