import { addBeats, beat, contract, marked, tick, tock } from "./metronome.ts";

export const metronome = contract({ beat, addBeats, tick, tock, marked });
